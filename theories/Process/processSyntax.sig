-- This is the current signature file being used, fewer layers of syntax, witout the -P wrappers, we don't need a separate syntactic category

seq : Functor
prod : Functor

bool : Type
nat : Type
index : Type
label : Type
defIndex : Type
ptcp : Type
qsize : Type

val : Type
valBool : Type
boolB : bool -> valBool
valB : val -> valBool

schl : Type -- located sch pointing to restriction
sch : Type -- located sch or variable for one
schlT : schl -> ptcp -> sch -- instantiated schl only with this construtor, always containing a location

exp : Type
valE : valBool -> exp
andE : exp -> exp -> exp

msg : Type
msgp : Type

labelM : nat -> msg 
valM : valBool -> msg
schM : sch -> msg 
msgT : msg -> ptcp -> msgp

schli : Type
schliT : schl -> index -> schli

process : Type
SessReq : valBool -> nat -> qsize -> (sch -> process) -> process 
SessAcc : valBool -> ptcp -> (sch -> process) -> process
ValSend : sch -> index -> exp -> process -> process
ValRec  : sch -> index -> (valBool -> process) -> process
SessDel : sch -> index -> sch -> process -> process
SessRec : sch -> index -> (sch -> process) -> process
LabelSel : sch -> index -> label -> process -> process
LabelBr : sch -> index -> "seq" ("prod" (nat,process)) -> process
If : exp -> process -> process -> process
Par : process -> process -> process
Inact : process
ResCh : (schl -> process) -> process
ResVal : (val -> process) -> process
PCall : defIndex -> exp -> "seq" (sch) -> process
MsgQ : schli -> "seq" (msgp) -> process


