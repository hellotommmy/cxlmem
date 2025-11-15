theory CXLMEM6
  imports Main
begin

(* Executable, order-agnostic next-state enumerators by flat-mapping over list elements *)
(* how about using a third list for completed memory ops, and just prepend to that list, not involving
   very complicated non-linear patterns on both the response channels and the mress list. (now doing, using a mapping instead of a list to avoid having to find the pended result with same txid)
   or, even simpler, do not record the pending results in mress, just record every completed transaction with txid in mress. (implement in the future)
   even simpler is to use registers to hold read results, not keeping any issued/completed reads/writes. (implement in the future) *)

definition m0 :: "nat ⇒ int" where
  "m0 _ = 0"

type_synonym txid = nat
type_synonym mem = "nat ⇒ int"

datatype Memop = Read nat | Write nat int
datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop | NoEntry

fun perform_Memop :: "Memop ⇒ (nat ⇒ int) ⇒ ((nat ⇒ int) * int)" where
  "perform_Memop (Read i) m = (m, m i)"
| "perform_Memop (Write i v) m = (m (i := v), v)"

datatype Req = MemRd txid nat
datatype DRS = MemData txid int | MemData_NXM txid
datatype Rwd = MemWrite txid nat int
datatype NDR = Cmp txid | BI_ConflictAck txid

datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDRMsg NDR | DRSMsg DRS | BISnp

fun get_op_addr :: "mem_msg ⇒ nat" where
  "get_op_addr m = (case m of ReqMsg (MemRd txk i) ⇒ i | _ ⇒ 0)"

type_synonym regs = "nat ⇒ int"

record cxl_state =
  memory :: "nat ⇒ int"
  m2sreqs :: "Req list"
  m2srwds :: "Rwd list"
  s2mdrss :: "DRS list"
  s2mndrs :: "NDR list"
  counter :: nat

type_synonym state =
  "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * (txid ⇒ Memop_res)"
type_synonym state2 =
  "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * regs"

(* generic helpers *)
fun flatmap :: "('a ⇒ 'b list) ⇒ 'a list ⇒ 'b list" where
  "flatmap f [] = []"
| "flatmap f (x # xs) = f x @ flatmap f xs"

fun enum_ctx :: "'a list ⇒ ('a list * 'a * 'a list) list" where
  "enum_ctx [] = []"
| "enum_ctx (x#xs) = ([], x, xs) # map (λ(pre,y,suf). (x#pre, y, suf)) (enum_ctx xs)"

(* duplicated helper retained because later code uses this name *)
fun flat_map :: "('a ⇒ 'b list) ⇒ 'a list ⇒ 'b list" where
  "flat_map f [] = []"
| "flat_map f (x#xs) = f x @ flat_map f xs"

(* External steps: combine four kinds of transitions *)
fun external_nexts1 :: "state ⇒ state list" where
  "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
      [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Read i)))]"
| "external_nexts1 (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
      [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, mress (cnt := Pending cnt (Write i v)))]"
| "external_nexts1 _ = []"

fun external_nexts2 :: "state ⇒ state list" where
"external_nexts2 (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let cmp_choices = enum_ctx ndrs;
          wr_compl = flat_map (λ(pre1,x1,suf1).
                        case x1 of Cmp tx ⇒
                          (case mress tx of Pending tx (Write i v) ⇒
                               [(m, reqs, rwds, drss, pre1 @ suf1, cnt, mops, mress (tx := WrRes tx i v))] | _ ⇒ [])
                        | _ ⇒ []) cmp_choices;
          drs_choices = enum_ctx drss;
          rd_compl = flat_map (λ(pre1,x1,suf1).
                        case x1 of MemData tx v ⇒
                          (case mress tx of Pending tx (Read i) ⇒
                               [(m, reqs, rwds, pre1 @ suf1, ndrs, cnt, mops, mress (tx := RdRes tx i v))] | _ ⇒ [])
                        | _ ⇒ []) drs_choices
      in wr_compl @ rd_compl)"

fun external_nexts :: "state ⇒ state list" where
  "external_nexts s = external_nexts1 s @ external_nexts2 s"

inductive  external_step ::
  "((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    ⇒ ((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) ⇒ bool"
  (infix "⟶e" 50)
where
    "(m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) ⟶e
     (m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)"
  | "(m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) ⟶e
     (m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)"
  | "(m, reqs, rwds, drss, ndrs1 @ [Cmp txid] @ ndrs2, cnt, mops, mress) ⟶e
     (m, reqs, rwds, drss, ndrs1@ndrs2, cnt, mops, WrRes txid i v # mress)"
  | "(m, reqs, rwds, drss1 @ [MemData txid v] @ drss2, ndrss, cnt, mops, mress) ⟶e
     (m, reqs, rwds, drss1 @ drss2, ndrss, cnt, mops, RdRes txid i v # mress)"

fun internal_nexts :: "state ⇒ state list" where
"internal_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let req_choices = enum_ctx reqs;
          req_resp = flat_map (λ(pre1, x1, suf1).
                        case x1 of MemRd tx i ⇒
                          [(m, pre1 @ suf1, rwds, MemData tx (m i) # drss, ndrs, cnt, mops, mress)]) req_choices;
          rwd_choices = enum_ctx rwds;
          rwd_resp = flat_map (λ(pre1, x1, suf1).
                        case x1 of MemWrite tx i v ⇒
                          [(m(i := v), reqs, pre1 @ suf1, drss, Cmp tx # ndrs, cnt, mops, mress)]) rwd_choices
      in req_resp @ rwd_resp)"

inductive internal_step ::
  "((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    ⇒ ((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) ⇒ bool"
  (infix "⟶i" 50)
where
    "(m, reqs1 @ [MemRd txid i] @ reqs2, rwds, drss, ndrs, cnt, mops, mress) ⟶i
     (m, reqs1 @ reqs2, rwds, MemData txid (m i) # drss, ndrs, cnt, mops, mress)"
  | "(m, reqs, rwds1 @ [MemWrite txid i v] @ rwds2, drss, ndrs, cnt, mops, mress) ⟶i
     (m(i := v), reqs, rwds1 @ rwds2, drss, Cmp txid # ndrs, cnt, mops, mress)"

inductive system_step ::
  "((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)
    ⇒ ((nat ⇒ int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) ⇒ bool"
  (infix "⟶" 50)
where
    "tuple1 ⟶e tuple2 ⟹ tuple1 ⟶ tuple2"
  | "tuple1 ⟶i tuple2 ⟹ tuple1 ⟶ tuple2"

definition system_nexts :: "state ⇒ state list" where
  "system_nexts s = internal_nexts s @ external_nexts s"

(* Example initial state *)
definition mem3_42 :: "mem" where "mem3_42 = m0 (3 := 42)"
definition initial1 :: state where
  "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], (λtx. NoEntry))"

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

(* CoRR (Coherent Read-Read) litmus: R(x); R(x) should not observe “new then old”.
   Construct a scenario where the first read can complete with a newer value (via drss),
   while memory still holds the old value, so the second read can observe the old one. *)
definition LT_CORR :: state where
  "LT_CORR = (m0, [], [], [], [], 0, [Read 3, Write 3 56, Read 3], (λtx. NoEntry))"

(* Explore only result mappings *)
value "eval_until_end_ress 6 LT_CORR"

(* Single-core litmus helpers and examples *)
definition mem_set :: "(nat ⇒ int) ⇒ (nat * int) list ⇒ (nat ⇒ int)" where
  "mem_set m xs = fold (λiv f. f (fst iv := snd iv)) xs m"

definition mem_init :: "(nat * int) list ⇒ (nat ⇒ int)" where
  "mem_init xs = mem_set m0 xs"

definition mk_state :: "(nat * int) list ⇒ nat ⇒ Memop list ⇒ state" where
  "mk_state inits cnt mops = (mem_init inits, [], [], [], [], cnt, mops, (λtx. NoEntry))"

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

(* Read the memory value at address i from a state (helper: inspect terminal memory) *)
fun mem_at :: "state ⇒ nat ⇒ int" where
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
value "remdups (map (λs. mem_at s 3) (eval_until_end 8 LT_CoWW_same))"

(* CoWW (different addresses) and WR/RW (different addresses) as a comparison *)
value "eval_until_end_ress_nodup 6 LT_CoWW_diff"
value "eval_until_end_ress_nodup 6 LT_WR_diff2"
value "eval_until_end_ress_nodup 6 LT_RW_diff2"

end
