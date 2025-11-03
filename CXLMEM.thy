theory CXLMEM imports Main 
begin

fun mem :: "nat \<Rightarrow> int" where
  "mem _ = 0"

type_synonym txid = nat

datatype Memop = Read nat | Write nat int

datatype Memop_res = RdRes txid nat int | WrRes txid nat int | Pending txid Memop

fun perform_Memop :: "Memop \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> ((nat \<Rightarrow> int) * int)" where
  "perform_Memop (Read i) m = (m, m i)"
| "perform_Memop (Write i v) m = (m ( i := v ), v)"

datatype Req = MemRd txid nat

datatype DRS = MemData txid nat

datatype Rwd = MemWrite txid nat int

datatype mem_msg = ReqMsg Req | RwdMsg Rwd | BIRsp | NDR | DRSMsg DRS  | BISnp

fun get_op_addr :: "mem_msg \<Rightarrow> nat" where
  "get_op_addr m = (case m of (ReqMsg (MemRd txk i)) \<Rightarrow> i | _ \<Rightarrow> 0)"

record cxl_state =
  memory :: "nat \<Rightarrow> int"                  
  m2s_req_chan :: "Req list"      
  m2s_rwd_chan :: "Rwd list"
  s2m_drs_chan :: "DRS list"
  counter :: nat

(*
  input_events :: "Memop list"
  output_events:: "Memop_completed list"
*)

fun external_step :: "(cxl_state * Memop list * Memop_res list)  => (cxl_state * Memop list * Memop_res list)"
  where
    "external_step (xst, (Read i # mops), mress) = (xst \<lparr>counter := counter xst + 1 \<rparr>, mops, Pending (counter xst) (Read i) # mress)"





  


end
