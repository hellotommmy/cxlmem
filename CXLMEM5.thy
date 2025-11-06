theory CXLMEM5 imports Main 
begin

(* Executable, order-agnostic next-state enumerators by flat-mapping over list elements *)
(*how about using a third list for completed memory ops, so everything works.*)
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

datatype Req = MemRd txid nat
datatype DRS = MemData txid int
datatype Rwd = MemWrite txid nat int
datatype NDR = Cmp txid 

type_synonym state = "mem * Req list * Rwd list * DRS list * NDR list * nat * Memop list * Memop_res list"

(* enumerate all positions with (prefix, element, suffix) triples *)
fun enum_ctx :: "'a list \<Rightarrow> ('a list * 'a * 'a list) list" where
  "enum_ctx [] = []"
| "enum_ctx (x#xs) = ([], x, xs) # map (\<lambda>(pre,y,suf). (x#pre, y, suf)) (enum_ctx xs)"

(* flat_map helper *)
fun flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map f [] = []"
| "flat_map f (x#xs) = f x @ flat_map f xs"

(* External steps: combine four kinds of transitions *)
fun external_nexts :: "state \<Rightarrow> state list" where
  "external_nexts (m, reqs, rwds, drss, ndrs, cnt, Read i # mops, mress) =
      [(m, MemRd cnt i # reqs, rwds, drss, ndrs, cnt+1, mops, Pending cnt (Read i) # mress)]"
| "external_nexts (m, reqs, rwds, drss, ndrs, cnt, Write i v # mops, mress) =
      [(m, reqs, MemWrite cnt i v # rwds, drss, ndrs, cnt+1, mops, Pending cnt (Write i v) # mress)]"
| "external_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let cmp_choices = enum_ctx ndrs;
          pw_choices = enum_ctx mress;
          wr_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of Cmp tx \<Rightarrow>
                          flat_map (\<lambda>(pre2,x2,suf2).
                            case x2 of Pending tx' (Write i v) \<Rightarrow>
                              if tx = tx' then [(m, reqs, rwds, drss, pre1 @ suf1, cnt, mops, WrRes tx i v # pre2 @ suf2)] else []
                          | _ \<Rightarrow> []) pw_choices) cmp_choices;
          drs_choices = enum_ctx drss;
          pr_choices = enum_ctx mress;
          rd_compl = flat_map (\<lambda>(pre1,x1,suf1).
                        case x1 of MemData tx v \<Rightarrow>
                          flat_map (\<lambda>(pre2,x2,suf2).
                            case x2 of Pending tx' (Read i) \<Rightarrow>
                              if tx = tx' then [(m, reqs, rwds, pre1 @ suf1, ndrs, cnt, mops, RdRes tx i v # pre2 @ suf2)] else []
                          | _ \<Rightarrow> []) pr_choices) drs_choices
      in wr_compl @ rd_compl)"

(* Internal steps: consume one Req or one Rwd at any position *)
fun internal_nexts :: "state \<Rightarrow> state list" where
  "internal_nexts (m, reqs, rwds, drss, ndrs, cnt, mops, mress) = (
      let req_choices = enum_ctx reqs;
          rw_choices = enum_ctx rwds;
          from_reqs = flat_map (\<lambda>(pre,x,suf). case x of MemRd tx i \<Rightarrow>
                                 [(m, pre @ suf, rwds, MemData tx (read_mem m i) # drss, ndrs, cnt, mops, mress)]) req_choices;
          from_rwds = flat_map (\<lambda>(pre,x,suf). case x of MemWrite tx i v \<Rightarrow>
                                 [(write_mem m i v, reqs, pre @ suf, drss, Cmp tx # ndrs, cnt, mops, mress)]) rw_choices
      in from_reqs @ from_rwds)"

definition system_nexts :: "state \<Rightarrow> state list" where
  "system_nexts s = external_nexts s @ internal_nexts s"

(* Example initial state *)
definition mem3_42 :: "mem" where "mem3_42 = write_mem [] 3 42"

definition initial1 :: state where
  "initial1 = (mem3_42, [], [], [], [], 15, [Read 3], [])"

declare [[values_timeout = 5]]

value "external_nexts initial1"
value "system_nexts initial1"

end
