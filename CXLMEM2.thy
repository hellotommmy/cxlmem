theory CXLMEM2 imports Main 
begin
(*internal & external transitions are seen as inductive relations *)
definition mem :: "nat \<Rightarrow> int" where
  "mem _ = 0"

type_synonym txid = nat

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

(* Note: code_pred doesn't work well with function types (nat => int) *)
(* Alternative: manually derive next states using inductive_cases *)

definition mem3_42 :: "nat \<Rightarrow> int" where "mem3_42 = (mem (3 := 42))"

definition initial1 :: "(nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list" 
  where "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], [])"

(* Manually compute the next state from initial1 via external_step *)
definition next1_external :: "(nat => int) * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list"
  where "next1_external = (mem3_42, [MemRd 15 3], [], [], [], 16, [], [Pending 15 (Read 3)])"

(* Note: Cannot use 'value' on inductive predicates like \<leadsto>e *)
(* 'value' is only for functional computations, not for checking relations *)

thm external_step.intros(1)

(* Prove that this is indeed a valid transition *)
lemma initial1_to_next1_external: "initial1 \<leadsto>e next1_external"
  unfolding initial1_def next1_external_def mem3_42_def
 
  apply (rule external_step.intros(1))
  done

(* We can use 'value' to inspect the state values themselves *)
value "initial1"
value "next1_external"

(* To enumerate all possible next states, we need to manually apply each rule *)
(* For initial1, only the first external_step rule (Read) applies *)
lemma only_external_read_applies: 
  "initial1 \<leadsto>e s \<Longrightarrow> s = next1_external"
  unfolding initial1_def next1_external_def
  by (erule external_step.cases, auto)

(* No internal steps are possible from initial1 (empty req/rwd lists) *)
lemma no_internal_from_initial1:
  "\<not>(initial1 \<leadsto>i s)"
  unfolding initial1_def
  by (auto elim: internal_step.cases)

end
