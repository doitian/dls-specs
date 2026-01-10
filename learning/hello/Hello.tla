----- MODULE Hello -----
VARIABLE outputConsole
VARIABLE readByUser

Init == /\ outputConsole = ""
        /\ readByUser = ""
Write == /\ outputConsole = ""
         /\ outputConsole' = "Hello, World!"
         /\ readByUser' = readByUser
Read == /\ outputConsole # ""
        /\ readByUser' = outputConsole
        /\ outputConsole' = outputConsole
Next == Write \/ Read
vars == <<outputConsole, readByUser>>
Spec == Init /\ [][Next]_vars
========================