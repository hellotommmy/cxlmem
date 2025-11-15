theory CXLMEM6 imports Main 
begin

(* Executable, order-agnostic next-state enumerators by flat-mapping over list elements *)
(*how about using a third list for completed memory ops, and just prepend to that list, not involving 
very complicated non-linear patterns on both the response channels and the mress list. (now doing)
or even simpler, do not record the pending results in mress, just record every completed transaction with txid in mress. (implement in the future)
even simpler is to use registers to hold read results, not keeping any issued/completed reads/writes. (implement in the future)
 
.*)
definition m0 :: "nat \<Rightarrow> int" where
  "m0 _ = 0"

type_synonym txid = nat
type_synonym mem = "nat \<Rightarrow> int"

datatype Memop = Read nat | Write nat int

datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop | NoEntry

fun perform_Memop :: "Memop \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> ((nat \<Rightarrow> int) * int)" where
  "perform_Memop (Read i) m = (m, m i)"
| "perform_Memop (Write i v) m = (m ( i := v ), v)"

datatype Req = MemRd txid nat

datatype DRS = MemData txid int | MemData_NXM txid

datatype Rwd = MemWrite txid nat int

datatype NDR = Cmp txid | BI_ConflictAck txid

datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDRMsg NDR | DRSMsg DRS  | BISnp

fun get_op_addr :: "mem_msg \<Rightarrow> nat" where
  "get_op_addr m = (case m of (ReqMsg (MemRd txk i)) \<Rightarrow> i | _ \<Rightarrow> 0)"

type_synonym regs = "nat \<Rightarrow> int"

record cxl_state =
  memory :: "nat \<Rightarrow> int"                  
  m2sreqs :: "Req list"      
  m2srwds :: "Rwd list"
  s2mdrss :: "DRS list"
  s2mndrs :: "NDR list"
  counter :: nat
type_synonym state = "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * (txid \<Rightarrow> Memop_res)"
type_synonym state2 = "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * regs"
(*
  input_events :: "Memop list"
  output_events:: "Memop_completed list"
  cxl_state: memory * m2sreqs * m2srwds * s2mdrss * counter
*)

fun flatmap :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
    "flatmap f [] = []"
  | "flatmap f (x # xs) = f x @ flatmap f xs"

fun enum_ctx :: "'a list \<Rightarrow> ('a list * 'a * 'a list) list" where
  "enum_ctx [] = []"
| "enum_ctx (x#xs) = ([], x, xs) # map (\<lambda>(pre,y,suf). (x#pre, y, suf)) (enum_ctx xs)"

(* flat_map helper *)
fun flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map f [] = []"
| "flat_map f (x#xs) = f x @ flat_map f xs"

(* External steps: combine four kinds of transitions *)
fun external_nexts1 :: "state \<Rightarrow> state list" where
  "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
      [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, mress ( cnt := Pending cnt (Read i)))]"
| "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
      [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Write i v)))]"
| "external_nexts1 _ = []"

fun external_nexts2 :: "state \<Rightarrow> state list" where
"external_nexts2 (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let cmp_choices = enum_ctx ndrs;
          wr_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of Cmp tx \<Rightarrow>
                            (case mress tx of Pending tx (Write i v) \<Rightarrow>
                               [(m, reqs, rwds, drss, pre1 @ suf1, cnt, mops, mress (tx := WrRes tx i v)) ] | _ \<Rightarrow> [])
                        | _ \<Rightarrow> [])  cmp_choices;
          drs_choices = enum_ctx drss;
          rd_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of MemData tx v \<Rightarrow>
                            (case mress tx of Pending tx (Read i) \<Rightarrow>
                               [(m, reqs, rwds, pre1 @ suf1, ndrs, cnt, mops, mress (tx := RdRes tx i v)) ] | _ \<Rightarrow> [])
                          | _ \<Rightarrow> []) drs_choices
      in wr_compl @ rd_compl)"

fun external_nexts :: "state \<Rightarrow> state list" where
  "external_nexts s = external_nexts1 s @ external_nexts2 s"

inductive  external_step :: "((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  => ((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>e" 50)
  where 
    "(m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) \<leadsto>e (m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)"
  | "(m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) \<leadsto>e (m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)"
  | "(m, reqs, rwds, drss, ndrs1 @ [Cmp txid] @ ndrs2, cnt, mops, mress) \<leadsto>e (m, reqs, rwds, drss, ndrs1@ndrs2, cnt, mops, WrRes txid i v # mress)"
  | "(m, reqs, rwds, drss1 @ [MemData txid v] @ drss2, ndrss, cnt, mops, mress) \<leadsto>e (m, reqs, rwds, drss1 @ drss2, ndrss, cnt, mops, RdRes txid i v # mress)"


fun internal_nexts :: "state \<Rightarrow> state list" where
"internal_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let req_choices = enum_ctx reqs;
          req_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemRd tx i \<Rightarrow> [(m, pre1 @ suf1, rwds, MemData tx (m i) # drss, ndrs, cnt, mops, mress)]) req_choices;
          rwd_choices = enum_ctx rwds;
          rwd_resp = flat_map (\<lambda>(pre1, x1, suf1).
                        case x1 of MemWrite tx i v \<Rightarrow> [(m(i := v), reqs, pre1 @ suf1, drss, Cmp tx # ndrs, cnt, mops, mress)]) rwd_choices
      in req_resp @ rwd_resp)"


inductive internal_step :: "((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  => ((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>i" 50)
  where
    "(m, reqs1 @ [MemRd txid i] @ reqs2, rwds, drss, ndrs, cnt, mops, mress) \<leadsto>i (m, reqs1 @ reqs2, rwds, MemData txid (m i) # drss, ndrs, cnt, mops, mress)"
  | "(m, reqs, rwds1 @ [MemWrite txid i v] @ rwds2, drss, ndrs, cnt, mops, mress) \<leadsto>i (m(i := v), reqs, rwds1 @ rwds2, drss, Cmp txid # ndrs, cnt, mops, mress)"

inductive system_step :: "((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  => ((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>" 50)
  where
    "tuple1 \<leadsto>e tuple2 \<Longrightarrow> tuple1 \<leadsto> tuple2"
  | "tuple1 \<leadsto>i tuple2 \<Longrightarrow> tuple1 \<leadsto> tuple2"

definition system_nexts :: "state \<Rightarrow> state list"
  where
  "system_nexts s = internal_nexts s @ external_nexts s"

(* Example initial state *)
definition mem3_42 :: "mem" where "mem3_42 = m0 (3 := 42)"

definition initial1 :: state where
  "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], (\<lambda>tx. NoEntry))"

declare [[values_timeout = 5]]
      
value "external_nexts initial1"
value "system_nexts initial1"

(* Depth-bounded evaluator: expand until no next states or fuel exhausted *)
fun eval_until_end :: "nat ⇒ state ⇒ state list" where
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
fun mress_pairs_upto :: "nat ⇒ (nat ⇒ Memop_res) ⇒ (nat * Memop_res) list" where
  "mress_pairs_upto 0 f = []"
| "mress_pairs_upto (Suc n) f =
     (let acc = mress_pairs_upto n f;
          tx = n;
          r = f tx
      in if r = NoEntry then acc else acc @ [(tx, r)])"

fun mress_pairs :: "state ⇒ (nat * Memop_res) list" where
  "mress_pairs (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = mress_pairs_upto cnt mress"

(* Example: show only the meaningful tx->result entries along paths *)
value "map mress_pairs (eval_until_end 3 initial1)"

(* Only show meaningful mress mappings for final states along explored paths *)
fun eval_until_end_ress :: "nat ⇒ state ⇒ (nat * Memop_res) list list" where
  "eval_until_end_ress 0 s = [mress_pairs s]"
| "eval_until_end_ress (Suc k) s =
     (let ns = system_nexts s in
       if ns = [] then [mress_pairs s] else concat (map (eval_until_end_ress k) ns))"

(* Example *)
value "eval_until_end_ress 3 initial1"

(* CoRR (Coherent Read-Read) litmus: R(x); R(x) should not see newer then older.
   Construct a scenario where first read can complete with a newer value (via drss),
   while memory still holds the old value, so the second read can observe the old one. *)
definition LT_CORR :: state where
  "LT_CORR = (m0, [], [], [], [], 0, [Read 3,Write 3 56, Read 3], (\<lambda>tx. NoEntry))"

(* Explore only result mappings *)
value "eval_until_end_ress 6 LT_CORR"

(* Single-core litmus helpers and examples *)

definition mem_set :: "(nat ⇒ int) ⇒ (nat * int) list ⇒ (nat ⇒ int)" where
  "mem_set m xs = fold (λ(iv) f. f (fst iv := snd iv)) xs m"

definition mem_init :: "(nat * int) list ⇒ (nat ⇒ int)" where
  "mem_init xs = mem_set m0 xs"

definition mk_state :: "(nat * int) list ⇒ nat ⇒ Memop list ⇒ state" where
  "mk_state inits cnt mops = (mem_init inits, [], [], [], [], cnt, mops, (λtx. NoEntry))"

(* Litmus tests (single-core) *)

(* RR: two reads observe the same memory *)
definition LT_RR :: state where
  "LT_RR = mk_state [(3,42)] 0 [Read 3, Read 3]"

(* WW: two writes recorded in order (memory not updated in this variant) *)
definition LT_WW :: state where
  "LT_WW = mk_state [] 0 [Write 3 1, Write 3 2]"

(* WR (same addr): read-after-write — with current model (no mem update), read observes old value *)
definition LT_WR_same :: state where
  "LT_WR_same = mk_state [(3,0)] 0 [Write 3 1, Read 3]"

(* WR (diff addr): read to another address unaffected *)
definition LT_WR_diff :: state where
  "LT_WR_diff = mk_state [(3,0),(4,42)] 0 [Write 3 1, Read 4]"

(* RW: read then write — read must observe the old value by program order *)
definition LT_RW :: state where
  "LT_RW = mk_state [(5,7)] 0 [Read 5, Write 5 9]"

(* Show only result mappings for each litmus *)
value "eval_until_end_ress 6 LT_RR"
value "eval_until_end_ress 5 LT_WW"
value "eval_until_end_ress 5 LT_WR_same"
value "eval_until_end_ress 5 LT_WR_diff"
value "eval_until_end_ress 5 LT_RW"

(* ------ Dedup helpers (remove duplicates) ------ *)

(* For ress-only output, element type is (nat * Memop_res) list, which has executable equality *)
definition eval_until_end_ress_nodup :: "nat ⇒ state ⇒ (nat * Memop_res) list list" where
  "eval_until_end_ress_nodup n s = remdups (eval_until_end_ress n s)"

(* For full states, equality is not executable due to function fields.
   Project a comparable key that drops mem and summarizes mress to pairs. *)
type_synonym state_key =
  "Req list * Rwd list * DRS list * NDR list * nat * Memop list * (nat * Memop_res) list"

fun state_to_key :: "state ⇒ state_key" where
  "state_to_key (m, reqs, rwds, drss, ndrs, cnt, mops, mress) =
      (reqs, rwds, drss, ndrs, cnt, mops, mress_pairs_upto cnt mress)"

fun eval_until_end_keys :: "nat ⇒ state ⇒ state_key list" where
  "eval_until_end_keys 0 s = [state_to_key s]"
| "eval_until_end_keys (Suc k) s =
     (let ns = system_nexts s in
       if ns = [] then [state_to_key s] else concat (map (eval_until_end_keys k) ns))"

definition eval_until_end_keys_nodup :: "nat ⇒ state ⇒ state_key list" where
  "eval_until_end_keys_nodup n s = remdups (eval_until_end_keys n s)"

(* Examples *)
value "eval_until_end_ress_nodup 7 LT_RR"
value "eval_until_end_ress_nodup 6 LT_WW"
value "eval_until_end_ress_nodup 6 LT_WR_same"
value "eval_until_end_ress_nodup 6 LT_WR_diff"
value "eval_until_end_ress_nodup 6 LT_RW"
value "eval_until_end_keys_nodup 9 LT_CORR"

(* ---------- Well-formedness: disallow orphan responses (no response without matching pending) ---------- *)
fun wf_drss :: "DRS list ⇒ (txid ⇒ Memop_res) ⇒ bool" where
  "wf_drss [] m = True"
| "wf_drss (MemData tx _ # xs) m = (∃i. m tx = Pending tx (Read i)) ∧ wf_drss xs m"
| "wf_drss (MemData_NXM tx # xs) m = (∃i. m tx = Pending tx (Read i)) ∧ wf_drss xs m"

fun wf_ndrs :: "NDR list ⇒ (txid ⇒ Memop_res) ⇒ bool" where
  "wf_ndrs [] m = True"
| "wf_ndrs (Cmp tx # xs) m = (∃i v. m tx = Pending tx (Write i v)) ∧ wf_ndrs xs m"
| "wf_ndrs (BI_ConflictAck _ # xs) m = wf_ndrs xs m"

fun wf_state :: "state ⇒ bool" where
  "wf_state (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = wf_drss drss mress ∧ wf_ndrs ndrs mress"

definition system_nexts_wf :: "state ⇒ state list" where
  "system_nexts_wf s = filter wf_state (system_nexts s)"

(* Examples (well-formed-only expansions) *)
value "map mress_pairs (system_nexts_wf initial1)"
value "map mress_pairs (filter wf_state (eval_until_end 3 initial1))"


end
