---------------------- MODULE HourClock ---------------------
EXTENDS Naturals, TLC
VARIABLE
    \* @type: Int;
    hr
TypeInv == hr \in (1 .. 12)
Init == TypeInv
Next == (hr' = IF hr # 12 THEN hr + 1 ELSE 1)
Spec == Init /\ [][Next]_hr
-------------------------------------------------------------
THEOREM Spec => []TypeInv
==============================================================