theory CXLMEM6 imports Main 
begin

(* Executable, order-agnostic next-state enumerators by flat-mapping over list elements *)
(*how about using a third list for completed memory ops, and just prepend to that list, not involving 
very complicated non-linear patterns on both the response channels and the mress list.
or even simpler, do not record the pending results in mress, just record every completed transaction with txid in mress.
even simpler is to use registers to hold read results, not keeping any issued/completed reads/writes.
 
.*)
definition m0 :: "nat \<Rightarrow> int" where
  "m0 _ = 0"

type_synonym txid = nat
type_synonym mem = "nat \<Rightarrow> int"

datatype Memop = Read nat | Write nat int

datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop

fun perform_Memop :: "Memop \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> ((nat \<Rightarrow> int) * int)" where
  "perform_Memop (Read i) m = (m, m i)"
| "perform_Memop (Write i v) m = (m ( i := v ), v)"

datatype Req = MemRd txid nat

datatype DRS = MemData txid int

datatype Rwd = MemWrite txid nat int

datatype NDR = Cmp txid 
datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDRMsg NDR | DRSMsg DRS  | BISnp

fun get_op_addr :: "mem_msg \<Rightarrow> nat" where
  "get_op_addr m = (case m of (ReqMsg (MemRd txk i)) \<Rightarrow> i | _ \<Rightarrow> 0)"

record cxl_state =
  memory :: "nat \<Rightarrow> int"                  
  m2sreqs :: "Req list"      
  m2srwds :: "Rwd list"
  s2mdrss :: "DRS list"
  s2mndrs :: "NDR list"
  counter :: nat
type_synonym state = "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list"
(*
  input_events :: "Memop list"
  output_events:: "Memop_completed list"
  cxl_state: memory * m2sreqs * m2srwds * s2mdrss * counter
*)

inductive  external_step :: "((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  => ((nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>e" 50)
  where 
    "(m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) \<leadsto>e (m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)"
  | "(m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) \<leadsto>e (m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)"
  | "(m, reqs, rwds, drss, ndrs1 @ [Cmp txid] @ ndrs2, cnt, mops, mress1 @ [Pending txid (Write i v)] @ mress2) \<leadsto>e (m, reqs, rwds, drss, ndrs1@ndrs2, cnt, mops, WrRes txid i v # mress1 @ mress2)"
  | "(m, reqs, rwds, drss1 @ [MemData txid v] @ drss2, ndrss, cnt, mops, mress1 @ [Pending txid (Read i)] @ mress2) \<leadsto>e (m, reqs, rwds, drss1 @ drss2, ndrss, cnt, mops, RdRes txid i v # mress1 @ mress2)"


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


(* Example initial state *)
definition mem3_42 :: "mem" where "mem3_42 = m0 (3 := 42)"

definition initial1 :: state where
  "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], [])"

declare [[values_timeout = 5]]
      
value "external_nexts initial1"
value "system_nexts initial1"

end
