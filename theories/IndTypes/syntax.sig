action : Type
value : Type
gType : Type
lType : Type
nat : Type
dir : Type
list : Functor
prod : Functor
ch : Type
mysort : Type
ptcp : Type
carriedG : Type 
carriedL : Type 

GEnd : gType
GRec : (gType -> gType) -> gType
GMsg : action -> value -> gType -> gType
GBranch : action -> "list" ("prod" (nat,gType)) -> gType

VSort : mysort -> value
VLT : carriedL -> ptcp -> value

SBool : mysort 
SGType : carriedG -> mysort 

EEnd : lType
ERec : (lType -> lType) -> lType
EMsg : dir -> ch -> value -> lType -> lType
EBranch : dir -> ch -> "list" ("prod" (nat,lType)) -> lType