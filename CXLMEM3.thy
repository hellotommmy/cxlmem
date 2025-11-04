theory CXLMEM3 imports Main 
begin
(* memory as finite association list: still code_pred has difficulty showing inductive relations between two states in a transition *)

type_synonym mem = "(nat * int) list"

fun read_mem :: "mem \<Rightarrow> nat \<Rightarrow> int" where
  "read_mem [] i = 0"
| "read_mem ((j,v)#xs) i = (if i = j then v else read_mem xs i)"

fun write_mem :: "mem \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> mem" where
  "write_mem [] i v = [(i, v)]"
| "write_mem ((j,w)#xs) i v = (if i = j then (i, v)#xs else (j, w)#write_mem xs i v)"

type_synonym txid = nat

datatype Memop = Read nat | Write nat int

datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop

fun perform_Memop :: "Memop \<Rightarrow> mem \<Rightarrow> (mem * int)" where
  "perform_Memop (Read i) m = (m, read_mem m i)"
| "perform_Memop (Write i v) m = (write_mem m i v, v)"

datatype Req = MemRd txid nat

datatype DRS = MemData txid int

datatype Rwd = MemWrite txid nat int

datatype NDR = Cmp txid 

datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDRMsg NDR | DRSMsg DRS  | BISnp

fun get_op_addr :: "mem_msg \<Rightarrow> nat" where
  "get_op_addr m = (case m of (ReqMsg (MemRd txk i)) \<Rightarrow> i | _ \<Rightarrow> 0)"

record cxl_state =
  memory :: "mem"                  
  m2sreqs :: "Req list"      
  m2srwds :: "Rwd list"
  s2mdrss :: "DRS list"
  s2mndrs :: "NDR list"
  counter :: nat

(* Transitions over tupled state for executability *)

inductive  external_step :: "(mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  \<Rightarrow> (mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>e" 50)
  where 
    "(m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) \<leadsto>e (m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)"
  | "(m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) \<leadsto>e (m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)"
  | "(m, reqs, rwds, drss, ndrs1 @ [Cmp txid] @ ndrs2, cnt, mops, mress1 @ [Pending txid (Write i v)] @ mress2) \<leadsto>e (m, reqs, rwds, drss, ndrs1@ndrs2, cnt, mops, WrRes txid i v # mress1 @ mress2)"
  | "(m, reqs, rwds, drss1 @ [MemData txid v] @ drss2, ndrss, cnt, mops, mress1 @ [Pending txid (Read i)] @ mress2) \<leadsto>e (m, reqs, rwds, drss1 @ drss2, ndrss, cnt, mops, RdRes txid i v # mress1 @ mress2)"


inductive internal_step :: "(mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  \<Rightarrow> (mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>i" 50)
  where
    "(m, reqs1 @ [MemRd txid i] @ reqs2, rwds, drss, ndrs, cnt, mops, mress) \<leadsto>i (m, reqs1 @ reqs2, rwds, MemData txid (read_mem m i) # drss, ndrs, cnt, mops, mress)"
  | "(m, reqs, rwds1 @ [MemWrite txid i v] @ rwds2, drss, ndrs, cnt, mops, mress) \<leadsto>i (write_mem m i v, reqs, rwds1 @ rwds2, drss, Cmp txid # ndrs, cnt, mops, mress)"

inductive system_step :: "(mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list)  \<Rightarrow> (mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list) \<Rightarrow> bool"
  (infix "\<leadsto>" 50)
  where
    "tuple1 \<leadsto>e tuple2 \<Longrightarrow> tuple1 \<leadsto> tuple2"
  | "tuple1 \<leadsto>i tuple2 \<Longrightarrow> tuple1 \<leadsto> tuple2"

definition mem3_42 :: "mem" where "mem3_42 = write_mem [] 3 42"

definition initial1 :: "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list" 
  where "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], [])"

definition next1_external :: "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list"
  where "next1_external = (mem3_42, [MemRd 15 3], [], [], [], 16, [], [Pending 15 (Read 3)])"

lemma initial1_to_next1_external: "initial1 \<leadsto>e next1_external"
  unfolding initial1_def next1_external_def mem3_42_def
  apply simp
  by (metis external_step.intros(1) numeral_plus_one semiring_norm(2,8))


(* Executable next-state functions to avoid code_pred limitations with list patterns *)

type_synonym state = "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list"

(* Enumerators for list occurrences *)
fun enum_memrd :: "Req list \<Rightarrow> (Req list * txid * nat * Req list) list" where
  "enum_memrd [] = []"
| "enum_memrd (MemRd tx i # rs) = ([], tx, i, rs) # map (\<lambda>(pref,tx',i',suf). (MemRd tx i # pref, tx', i', suf)) (enum_memrd rs)"

fun enum_memwrite :: "Rwd list \<Rightarrow> (Rwd list * txid * nat * int * Rwd list) list" where
  "enum_memwrite [] = []"
| "enum_memwrite (MemWrite tx i v # rs) = ([], tx, i, v, rs) # map (\<lambda>(pref,tx',i',v',suf). (MemWrite tx i v # pref, tx', i', v', suf)) (enum_memwrite rs)"

fun enum_cmp :: "NDR list \<Rightarrow> (NDR list * txid * NDR list) list" where
  "enum_cmp [] = []"
| "enum_cmp (Cmp tx # rs) = ([], tx, rs) # map (\<lambda>(pref,tx',suf). (Cmp tx # pref, tx', suf)) (enum_cmp rs)"

fun enum_memdata :: "DRS list \<Rightarrow> (DRS list * txid * int * DRS list) list" where
  "enum_memdata [] = []"
| "enum_memdata (MemData tx v # rs) = ([], tx, v, rs) # map (\<lambda>(pref,tx',v',suf). (MemData tx v # pref, tx', v', suf)) (enum_memdata rs)"

fun enum_pending_read :: "Memop_res list \<Rightarrow> (Memop_res list * txid * nat * Memop_res list) list" where
  "enum_pending_read [] = []"
| "enum_pending_read (Pending tx (Read i) # rs) = ([], tx, i, rs) # map (\<lambda>(pref,tx',i',suf). (Pending tx (Read i) # pref, tx', i', suf)) (enum_pending_read rs)"
| "enum_pending_read (r # rs) = map (\<lambda>(pref,tx,i,suf). (r # pref, tx, i, suf)) (enum_pending_read rs)"

fun enum_pending_write :: "Memop_res list \<Rightarrow> (Memop_res list * txid * nat * int * Memop_res list) list" where
  "enum_pending_write [] = []"
| "enum_pending_write (Pending tx (Write i v) # rs) = ([], tx, i, v, rs) # map (\<lambda>(pref,tx',i',v',suf). (Pending tx (Write i v) # pref, tx', i', v', suf)) (enum_pending_write rs)"
| "enum_pending_write (r # rs) = map (\<lambda>(pref,tx,i,v,suf). (r # pref, tx, i, v, suf)) (enum_pending_write rs)"

fun external_nexts :: "state \<Rightarrow> state list" where
  "external_nexts (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
     [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)]"
| "external_nexts (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
     [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)]"
| "external_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) =
     (let nd_steps = map (\<lambda>(pref,tx,suf).
                       map (\<lambda>(mpref,tx2,i,v,msuf). (m, reqs, rwds, drss, pref @ suf, cnt, mops, WrRes tx i v # mpref @ msuf))
                           (filter (\<lambda>(mp,tx2,_,_,_). tx2 = tx) (enum_pending_write mress))) (enum_cmp ndrs);
          drs_steps = map (\<lambda>(dpref,tx,v,dsuf).
                       map (\<lambda>(mpref,tx2,i,msuf). (m, reqs, rwds, dpref @ dsuf, ndrs, cnt, mops, RdRes tx i v # mpref @ msuf))
                           (filter (\<lambda>(mp,tx2,_,_). tx2 = tx) (enum_pending_read mress))) (enum_memdata drss)
      in concat nd_steps @ concat drs_steps)"

fun internal_nexts :: "state \<Rightarrow> state list" where
  "internal_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
     map (\<lambda>(pref,tx,i,suf). (m, pref @ suf, rwds, MemData tx (read_mem m i) # drss, ndrs, cnt, mops, mress)) (enum_memrd reqs)
     @ map (\<lambda>(pref,tx,i,v,suf). (write_mem m i v, reqs, pref @ suf, drss, Cmp tx # ndrs, cnt, mops, mress)) (enum_memwrite rwds)
   )"

fun system_nexts :: "state \<Rightarrow> state list" where
  "system_nexts s = external_nexts s @ internal_nexts s"

declare [[values_timeout = 5]]

value "external_nexts initial1"
value "system_nexts initial1"

end

