theory CXLMEM9
  imports Main
begin

(* Executable, order-agnostic next-state enumerators by flat-mapping over list elements *)
(* how about using a third list for completed memory ops, and just prepend to that list, not involving
   very complicated non-linear patterns on both the response channels and the mress list. (now doing, using a mapping instead of a list to avoid having to find the pended result with same txid)
   or, even simpler, do not record the pending results in mress, just record every completed transaction with txid in mress. (implement in the future)
   even simpler is to use registers to hold read results, not keeping any issued/completed reads/writes. (implement in the future) *)

definition m0 :: "nat \<Rightarrow> int" where
  "m0 _ = 0"

type_synonym txid = nat
type_synonym mem = "nat \<Rightarrow> int"

datatype Memop = Read nat | Write nat int
datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop | NoEntry

fun perform_Memop :: "Memop \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> ((nat \<Rightarrow> int) * int)" where
  "perform_Memop (Read i) m = (m, m i)"
| "perform_Memop (Write i v) m = (m (i := v), v)"

datatype Req = MemRd txid nat
datatype DRS = MemData txid int | MemData_NXM txid
datatype Rwd = MemWrite txid nat int
datatype NDR = Cmp txid | BI_ConflictAck txid

datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDRMsg NDR | DRSMsg DRS | BISnp

fun get_op_addr :: "mem_msg \<Rightarrow> nat" where
  "get_op_addr m = (case m of ReqMsg (MemRd txk i) \<Rightarrow> i | _ \<Rightarrow> 0)"

type_synonym regs = "nat \<Rightarrow> int"

record cxl_state =
  memory :: "nat \<Rightarrow> int"
  m2sreqs :: "Req list"
  m2srwds :: "Rwd list"
  s2mdrss :: "DRS list"
  s2mndrs :: "NDR list"
  counter :: nat

type_synonym state =
  "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * (txid \<Rightarrow> Memop_res)"
type_synonym state2 =
  "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * regs"

(* generic helpers *)
fun flatmap :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flatmap f [] = []"
| "flatmap f (x # xs) = f x @ flatmap f xs"

fun enum_ctx_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a * 'a list) list" where
  "enum_ctx_aux [] acc = []"
| "enum_ctx_aux (x # xs) acc = (List.rev acc, x, xs) # enum_ctx_aux xs (x # acc)"

fun enum_ctx_maybe_more_efficient :: "'a list \<Rightarrow> ('a list * 'a * 'a list) list" where
  "enum_ctx_maybe_more_efficient xs = enum_ctx_aux xs []"


fun enum_ctx :: "'a list \<Rightarrow> ('a list * 'a * 'a list) list" where
  "enum_ctx [] = []"
| "enum_ctx (x#xs) = ([], x, xs) # map (\<lambda>(pre,y,suf). (x#pre, y, suf)) (enum_ctx xs)"

(* duplicated helper retained because later code uses this name *)
fun flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map f [] = []"
| "flat_map f (x#xs) = f x @ flat_map f xs"

\<comment>\<open> ------ Guards for Memory Consistency ------ \<close>

\<comment>\<open> Extract address from a Memop \<close>
fun get_memop_addr :: "Memop \<Rightarrow> nat option" where
  "get_memop_addr (Read i) = Some i"
| "get_memop_addr (Write i v) = Some i"

\<comment>\<open> Check if there is a pending write to address addr in mress mapping.
   Scan through all possible transaction IDs up to cnt. \<close>
fun has_pending_write_to_addr :: "nat \<Rightarrow> (nat \<Rightarrow> Memop_res) \<Rightarrow> nat \<Rightarrow> bool" where
  "has_pending_write_to_addr 0 mress addr = False"
| "has_pending_write_to_addr (Suc n) mress addr =
     (case mress n of
        Pending tx (Write i v) \<Rightarrow> if i = addr then True else has_pending_write_to_addr n mress addr
      | _ \<Rightarrow> has_pending_write_to_addr n mress addr)"

\<comment>\<open> Guard: allow read to address i only if no pending write to same address exists \<close>
fun can_issue_read :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> Memop_res) \<Rightarrow> bool" where
  "can_issue_read addr cnt mress = (\<not> has_pending_write_to_addr cnt mress addr)"

\<comment>\<open> Guard: allow processing MemRd request only if no pending write to same address \<close>
fun can_process_read :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> Memop_res) \<Rightarrow> bool" where
  "can_process_read addr cnt mress = (\<not> has_pending_write_to_addr cnt mress addr)"

\<comment>\<open> ------ End Guards ------ \<close>

(* External steps: combine four kinds of transitions *)
fun external_nexts1 :: "state \<Rightarrow> state list" where
  "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
      [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Read i)))]"
| "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
      [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Write i v)))]"
| "external_nexts1 _ = []"

fun external_nexts2 :: "state \<Rightarrow> state list" where
"external_nexts2 (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let cmp_choices = enum_ctx ndrs;
          wr_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of Cmp tx \<Rightarrow>
                          (case mress tx of Pending tx (Write i v) \<Rightarrow>
                               [(m, reqs, rwds, drss, pre1 @ suf1, cnt, mops, mress (tx := WrRes tx i v))] | _ \<Rightarrow> [])
                        | _ \<Rightarrow> []) cmp_choices;
          drs_choices = enum_ctx drss;
          rd_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of MemData tx v \<Rightarrow>
                          (case mress tx of Pending tx (Read i) \<Rightarrow>
                               [(m, reqs, rwds, pre1 @ suf1, ndrs, cnt, mops, mress (tx := RdRes tx i v))] | _ \<Rightarrow> [])
                        | _ \<Rightarrow> []) drs_choices
      in wr_compl @ rd_compl)"

fun external_nexts :: "state \<Rightarrow> state list" where
  "external_nexts s = external_nexts1 s @ external_nexts2 s"

\<comment>\<open> ------ Guarded versions ------ \<close>

\<comment>\<open> External steps WITH guard: prevent read when write to same address is pending \<close>
fun external_nexts1_guarded :: "state \<Rightarrow> state list" where
  "external_nexts1_guarded (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
      (if can_issue_read i cnt mress
       then [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Read i)))]
       else [])"
|| "external_nexts1_guarded (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
      [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Write i v)))]"
|| "external_nexts1_guarded _ = []"

fun external_nexts_guarded :: "state \<Rightarrow> state list" where
  "external_nexts_guarded s = external_nexts1_guarded s @ external_nexts2 s"

\<comment>\<open> Internal steps WITH guard: prevent processing read when write to same address is pending \<close>
fun internal_nexts_guarded :: "state \<Rightarrow> state list" where
"internal_nexts_guarded (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let req_choices = enum_ctx reqs;
          req_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemRd tx i \<Rightarrow>
                          if can_process_read i cnt mress
                          then [(m, pre1 @ suf1, rwds, MemData tx (m i) # drss, ndrs, cnt, mops, mress)]
                          else []) req_choices;
          rwd_choices = enum_ctx rwds;
          rwd_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemWrite tx i v \<Rightarrow>
                          [(m(i := v), reqs, pre1 @ suf1, drss, Cmp tx # ndrs, cnt, mops, mress)]) rwd_choices
      in req_resp @ rwd_resp)"

definition system_nexts_guarded :: "state \<Rightarrow> state list" where
  "system_nexts_guarded s = internal_nexts_guarded s @ external_nexts_guarded s"

\<comment>\<open> ------ End guarded versions ------ \<close>

inductive  external_step ::
  "((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    \<Rightarrow> ((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<longrightarrow>e" 50)
where
    "(m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) \<longrightarrow>e
     (m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)"
  | "(m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) \<longrightarrow>e
     (m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)"
  | "(m, reqs, rwds, drss, ndrs1 @ [Cmp txid] @ ndrs2, cnt, mops, mress) \<longrightarrow>e
     (m, reqs, rwds, drss, ndrs1@ndrs2, cnt, mops, WrRes txid i v # mress)"
  | "(m, reqs, rwds, drss1 @ [MemData txid v] @ drss2, ndrss, cnt, mops, mress) \<longrightarrow>e
     (m, reqs, rwds, drss1 @ drss2, ndrss, cnt, mops, RdRes txid i v # mress)"

fun internal_nexts :: "state \<Rightarrow> state list" where
"internal_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let req_choices = enum_ctx reqs;
          req_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemRd tx i \<Rightarrow>
                          [(m, pre1 @ suf1, rwds, MemData tx (m i) # drss, ndrs, cnt, mops, mress)]) req_choices;
          rwd_choices = enum_ctx rwds;
          rwd_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemWrite tx i v \<Rightarrow>
                          [(m(i := v), reqs, pre1 @ suf1, drss, Cmp tx # ndrs, cnt, mops, mress)]) rwd_choices
      in req_resp @ rwd_resp)"

inductive internal_step ::
  "((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    \<Rightarrow> ((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<longrightarrow>i" 50)
where
    "(m, reqs1 @ [MemRd txid i] @ reqs2, rwds, drss, ndrs, cnt, mops, mress) \<longrightarrow>i
     (m, reqs1 @ reqs2, rwds, MemData txid (m i) # drss, ndrs, cnt, mops, mress)"
  | "(m, reqs, rwds1 @ [MemWrite txid i v] @ rwds2, drss, ndrs, cnt, mops, mress) \<longrightarrow>i
     (m(i := v), reqs, rwds1 @ rwds2, drss, Cmp txid # ndrs, cnt, mops, mress)"

inductive system_step ::
  "((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    \<Rightarrow> ((nat \<Rightarrow> int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<longrightarrow>" 50)
where
    "tuple1 \<longrightarrow>e tuple2 \<Longrightarrow> tuple1 \<longrightarrow> tuple2"
  | "tuple1 \<longrightarrow>i tuple2 \<Longrightarrow> tuple1 \<longrightarrow> tuple2"

definition system_nexts :: "state \<Rightarrow> state list" where
  "system_nexts s = internal_nexts s @ external_nexts s"

(* Example initial state *)
definition mem3_42 :: "mem" where "mem3_42 = m0 (3 := 42)"
definition initial1 :: state where
  "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], (\<lambda>tx. NoEntry))"

declare [[values_timeout = 5]]

value "external_nexts initial1"
value "system_nexts initial1"

(* Depth-bounded evaluator: expand until no next states or fuel exhausted *)
fun eval_until_end :: "nat \<Rightarrow> state \<Rightarrow> state list" where
  "eval_until_end 0 s = [s]"
| "eval_until_end (Suc k) s =
     (let ns = system_nexts s in
       if ns = [] then [s] else concat (map (eval_until_end k) ns))"

(* Examples *)
value "eval_until_end 0 initial1"
value "eval_until_end 1 initial1"
value "eval_until_end 2 initial1"
value "eval_until_end 3 initial1"
value "eval_until_end 4 initial1"
value "eval_until_end 5 initial1"

(* Collect meaningful (txid, Memop_res) pairs from the tx->result map
   We scan tx in [0 ..< cnt], treating NoEntry as empty. *)
fun mress_pairs_upto :: "nat \<Rightarrow> (nat \<Rightarrow> Memop_res) \<Rightarrow> (nat * Memop_res) list" where
  "mress_pairs_upto 0 f = []"
| "mress_pairs_upto (Suc n) f =
     (let acc = mress_pairs_upto n f;
          tx = n;
          r = f tx
      in if r = NoEntry then acc else acc @ [(tx, r)])"

fun mress_pairs :: "state \<Rightarrow> (nat * Memop_res) list" where
  "mress_pairs (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = mress_pairs_upto cnt mress"

(* Example: show only the meaningful tx->result entries along paths *)
value "map mress_pairs (eval_until_end 3 initial1)"

(* Only show meaningful mress mappings for final states along explored paths *)
fun eval_until_end_ress :: "nat \<Rightarrow> state \<Rightarrow> (nat * Memop_res) list list" where
  "eval_until_end_ress 0 s = [mress_pairs s]"
| "eval_until_end_ress (Suc k) s =
     (let ns = system_nexts s in
       if ns = [] then [mress_pairs s] else concat (map (eval_until_end_ress k) ns))"

(* Example *)
value "eval_until_end_ress 3 initial1"

\<comment>\<open> Guarded version: uses system_nexts_guarded instead of system_nexts \<close>
fun eval_until_end_ress_guarded :: "nat \<Rightarrow> state \<Rightarrow> (nat * Memop_res) list list" where
  "eval_until_end_ress_guarded 0 s = [mress_pairs s]"
|| "eval_until_end_ress_guarded (Suc k) s =
     (let ns = system_nexts_guarded s in
       if ns = [] then [mress_pairs s] else concat (map (eval_until_end_ress_guarded k) ns))"

\<comment>\<open> ------ Incoherence Detection ------ \<close>

\<comment>\<open> Extract address and value from a Memop_res if it's a read or write result \<close>
fun get_addr_val :: "Memop_res \<Rightarrow> (nat * int) option" where
  "get_addr_val (RdRes _ addr val) = Some (addr, val)"
| "get_addr_val (WrRes _ addr val) = Some (addr, val)"
| "get_addr_val _ = None"

\<comment>\<open> Filter operations for a specific address from a trace \<close>
fun filter_addr_ops :: "nat \<Rightarrow> (nat * Memop_res) list \<Rightarrow> (nat * Memop_res) list" where
  "filter_addr_ops addr [] = []"
| "filter_addr_ops addr ((tx, res) # rest) =
     (case get_addr_val res of
        Some (a, v) \<Rightarrow> if a = addr then (tx, res) # filter_addr_ops addr rest
                                  else filter_addr_ops addr rest
      | None \<Rightarrow> filter_addr_ops addr rest)"

\<comment>\<open> Extract all addresses mentioned in a trace \<close>
fun get_all_addrs :: "(nat * Memop_res) list \<Rightarrow> nat list" where
  "get_all_addrs [] = []"
| "get_all_addrs ((tx, res) # rest) =
     (case get_addr_val res of
        Some (addr, _) \<Rightarrow> addr # get_all_addrs rest
      | None \<Rightarrow> get_all_addrs rest)"

\<comment>\<open> Helper: check if a list of read values violates coherence \<close>
fun check_read_pairs :: "int list \<Rightarrow> bool" where
  "check_read_pairs [] = True"
| "check_read_pairs [_] = True"
| "check_read_pairs (v1 # v2 # rest) =
     (if v1 \<noteq> 0 \<and> v2 = 0 \<and> v1 \<noteq> v2 then False  \<comment>\<open> new then old: incoherent \<close>
      else check_read_pairs (v2 # rest))"

\<comment>\<open> Check if a single trace violates coherence for a specific address.
   Violation occurs if two reads see decreasing values (newer then older).
   This detects the "read new, then read old" pattern after a write. \<close>
fun check_addr_coherence :: "nat \<Rightarrow> (nat * Memop_res) list \<Rightarrow> bool" where
  "check_addr_coherence addr trace =
     (let ops = filter_addr_ops addr trace;
          reads = filter (\<lambda>(tx, res). case res of RdRes _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) ops
      in case reads of
           [] \<Rightarrow> True  \<comment>\<open> no reads, trivially coherent \<close>
         | [_] \<Rightarrow> True  \<comment>\<open> single read, trivially coherent \<close>
         | _ \<Rightarrow> \<comment>\<open> check if any pair of consecutive reads violates coherence \<close>
             let read_vals = map (\<lambda>(tx, res). case res of RdRes _ _ v \<Rightarrow> v | _ \<Rightarrow> 0) reads
             in check_read_pairs read_vals)"

\<comment>\<open> Simplified coherence check: detect if reads observe "new value then old value"
   Specifically for the pattern: RdRes _ addr old, WrRes _ addr new, RdRes _ addr old
   where new \<noteq> old \<close>
fun has_incoherence_simple :: "(nat * Memop_res) list \<Rightarrow> bool" where
  "has_incoherence_simple trace =
     (let addrs = remdups (get_all_addrs trace)
      in \<not> (fold (\<lambda>addr acc. acc \<and> check_addr_coherence addr trace) addrs True))"

\<comment>\<open> Check if any trace in a list exhibits incoherence \<close>
fun has_any_incoherence :: "(nat * Memop_res) list list \<Rightarrow> bool" where
  "has_any_incoherence traces = (filter has_incoherence_simple traces \<noteq> [])"

\<comment>\<open> Count how many traces exhibit incoherence \<close>
fun count_incoherent :: "(nat * Memop_res) list list \<Rightarrow> nat" where
  "count_incoherent traces = length (filter has_incoherence_simple traces)"

\<comment>\<open> Filter out only the incoherent traces \<close>
fun filter_incoherent :: "(nat * Memop_res) list list \<Rightarrow> (nat * Memop_res) list list" where
  "filter_incoherent traces = filter has_incoherence_simple traces"

\<comment>\<open> ------ End Incoherence Detection ------ \<close>

(* CoRR (Coherent Read-Read) litmus: R(x); R(x) should not observe "new then old".
   Construct a scenario where the first read can complete with a newer value (via drss),
   while memory still holds the old value, so the second read can observe the old one. *)
definition LT_CORR :: state where
  "LT_CORR = (m0, [], [], [], [], 0, [Read 3, Write 3 56, Read 3], (\<lambda>tx. NoEntry))"

(* Explore only result mappings *)
value "eval_until_end_ress 6 LT_CORR"

(* Test incoherence detection on LT_CORR *)
value "let results = eval_until_end_ress 10 LT_CORR in
         (length results, count_incoherent results, has_any_incoherence results)"

\<comment>\<open> ------ Guard Testing ------ \<close>

\<comment>\<open> Comparison: WITHOUT guard vs WITH guard \<close>

\<comment>\<open> Test WITHOUT guard (original behavior) - uses eval_until_end_ress \<close>
value "let results = eval_until_end_ress 6 LT_CORR in
         (length results, count_incoherent results, has_any_incoherence results)"

\<comment>\<open> Test WITH guard (should reduce or eliminate incoherence) - uses eval_until_end_ress_guarded \<close>
value "let results = eval_until_end_ress_guarded 6 LT_CORR in
         (length results, count_incoherent results, has_any_incoherence results)"

\<comment>\<open> Show unique traces WITHOUT guard \<close>
value "remdups (eval_until_end_ress 6 LT_CORR)"

\<comment>\<open> Show unique traces WITH guard \<close>
value "remdups (eval_until_end_ress_guarded 6 LT_CORR)"

\<comment>\<open> Filter and show only incoherent traces WITHOUT guard \<close>
value "remdups (filter_incoherent (eval_until_end_ress 6 LT_CORR))"

\<comment>\<open> Filter and show only incoherent traces WITH guard (should be empty or fewer) \<close>
value "remdups (filter_incoherent (eval_until_end_ress_guarded 6 LT_CORR))"

(* Single-core litmus helpers and examples *)
definition mem_set :: "(nat \<Rightarrow> int) \<Rightarrow> (nat * int) list \<Rightarrow> (nat \<Rightarrow> int)" where
  "mem_set m xs = fold (\<lambda>iv f. f (fst iv := snd iv)) xs m"

definition mem_init :: "(nat * int) list \<Rightarrow> (nat \<Rightarrow> int)" where
  "mem_init xs = mem_set m0 xs"

definition mk_state :: "(nat * int) list \<Rightarrow> nat \<Rightarrow> Memop list \<Rightarrow> state" where
  "mk_state inits cnt mops = (mem_init inits, [], [], [], [], cnt, mops, (\<lambda>tx. NoEntry))"

(* Litmus tests (single core) *)
definition LT_RR :: state where
  "LT_RR = mk_state [(3,42)] 0 [Read 3, Read 3]"

definition LT_WW :: state where
  "LT_WW = mk_state [] 0 [Write 3 1, Write 3 2]"

definition LT_WR_same :: state where
  "LT_WR_same = mk_state [(3,0)] 0 [Write 3 1, Read 3]"

definition LT_WR_diff :: state where
  "LT_WR_diff = mk_state [(3,0),(4,42)] 0 [Write 3 1, Read 4]"

definition LT_RW :: state where
  "LT_RW = mk_state [(5,7)] 0 [Read 5, Write 5 9]"

(* Show only result mappings for each litmus *)
value "eval_until_end_ress 6 LT_RR"
value "eval_until_end_ress 5 LT_WW"
value "eval_until_end_ress 5 LT_WR_same"
value "eval_until_end_ress 5 LT_WR_diff"
value "eval_until_end_ress 5 LT_RW"

(* ------ De-dup helpers (remove duplicates) ------ *)

(* For ress-only output, element type is (nat * Memop_res) list, which has executable equality *)
definition eval_until_end_ress_nodup :: "nat \<Rightarrow> state \<Rightarrow> (nat * Memop_res) list list" where
  "eval_until_end_ress_nodup n s = remdups (eval_until_end_ress n s)"

(* For full states, equality is not executable due to function fields.
   Project a comparable key that drops mem and summarizes mress to pairs. *)
type_synonym state_key =
  "Req list * Rwd list * DRS list * NDR list * nat * Memop list * (nat * Memop_res) list"

fun state_to_key :: "state \<Rightarrow> state_key" where
  "state_to_key (m, reqs, rwds, drss, ndrs, cnt, mops, mress) =
      (reqs, rwds, drss, ndrs, cnt, mops, mress_pairs_upto cnt mress)"

fun eval_until_end_keys :: "nat \<Rightarrow> state \<Rightarrow> state_key list" where
  "eval_until_end_keys 0 s = [state_to_key s]"
| "eval_until_end_keys (Suc k) s =
     (let ns = system_nexts s in
       if ns = [] then [state_to_key s] else concat (map (eval_until_end_keys k) ns))"

definition eval_until_end_keys_nodup :: "nat \<Rightarrow> state \<Rightarrow> state_key list" where
  "eval_until_end_keys_nodup n s = remdups (eval_until_end_keys n s)"

(* Examples *)
value "eval_until_end_ress_nodup 7 LT_RR"
value "eval_until_end_ress_nodup 6 LT_WW"
value "eval_until_end_ress_nodup 6 LT_WR_same"
value "eval_until_end_ress_nodup 6 LT_WR_diff"
value "eval_until_end_ress_nodup 6 LT_RW"
value "eval_until_end_keys_nodup 9 LT_CORR"

(* Read the memory value at address i from a state (helper: inspect terminal memory) *)
fun mem_at :: "state \<Rightarrow> nat \<Rightarrow> int" where
  "mem_at (m, _, _, _, _, _, _, _) i = m i"

(* CoRR (Read; Read) — same thread reads the same address twice; should not observe “new then old” *)
definition LT_CoRR_ok :: state where
  "LT_CoRR_ok = mk_state [(3,42)] 0 [Read 3, Read 3]"

(* CoRR-violation scenario (your LT_CORR is similar): R; W; R — if the first read can see the new value but the second read sees the old value, this violates CoRR *)
definition LT_CoRR_bad :: state where
  "LT_CoRR_bad = mk_state [] 0 [Read 3, Write 3 56, Read 3]"

(* CoWR (same address): Write; Read — the read should at least see the value just written by the same thread *)
definition LT_CoWR_same :: state where
  "LT_CoWR_same = mk_state [(3,0)] 0 [Write 3 1, Read 3]"

(* CoRW: Read; Write (same address) — the first read must not “see into the future” *)
definition LT_CoRW1 :: state where
  "LT_CoRW1 = mk_state [(3,7)] 0 [Read 3, Write 3 9]"

(* CoRWR: Read; Write; Read (same address) — the two reads should be non-decreasing versions: cannot be “new then old” *)
definition LT_CoRWR :: state where
  "LT_CoRWR = mk_state [(3,0)] 0 [Read 3, Write 3 5, Read 3]"

(* CoWW: Write; Write same address — later write should be ordered after earlier write globally (SC-per-location) *)
definition LT_CoWW_same :: state where
  "LT_CoWW_same = mk_state [(3,0)] 0 [Write 3 1, Write 3 2]"

(* CoWW: different addresses — no strong ordering required *)
definition LT_CoWW_diff :: state where
  "LT_CoWW_diff = mk_state [(3,0),(4,100)] 0 [Write 3 1, Write 4 2]"

(* Two address-independent sanity checks: WR/RW to different addresses *)
definition LT_WR_diff2 :: state where
  "LT_WR_diff2 = mk_state [(3,0),(4,42)] 0 [Write 3 1, Read 4]"

definition LT_RW_diff2 :: state where
  "LT_RW_diff2 = mk_state [(3,7),(4,11)] 0 [Read 3, Write 4 9]"

declare [[values_timeout = 5]]

(* CoRR normal case: both reads should be 42 *)
value "eval_until_end_ress_nodup 6 LT_CoRR_ok"

(* CoRR violation case: it may produce result pairs that are [new then old] *)
value "eval_until_end_ress_nodup 7 LT_CoRR_bad"

(* CoWR (same address): the read should at least see 1; the current model may still show 0 — indicates a possible CoWR violation *)
value "eval_until_end_ress_nodup 7 LT_CoWR_same"

(* CoRW: the first read should be the old value 7 *)
value "eval_until_end_ress_nodup 7 LT_CoRW1"

(* CoRWR: pairs of the two read results — check whether (r1=5, r2=0) (new then old) can occur *)
value "eval_until_end_ress_nodup 8 LT_CoRWR"

(* CoWW end-state memory cell 3 value set; if {1,2} is a subset of this set, write–write reordering is possible for the same address *)
value "remdups (map (\<lambda>s. mem_at s 3) (eval_until_end 8 LT_CoWW_same))"

(* CoWW (different addresses) and WR/RW (different addresses) as a comparison *)
value "eval_until_end_ress_nodup 6 LT_CoWW_diff"
value "eval_until_end_ress_nodup 6 LT_WR_diff2"
value "eval_until_end_ress_nodup 6 LT_RW_diff2"

end
