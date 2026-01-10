-- Hour Clock specification in Alloy 6
open util/integer

one sig State {
  var hr: Int
}

-- HCini: hr is between 1 and 12
pred HCini {
  State.hr >= 1 and State.hr <= 12
}

pred HCnxt {
  State.hr' = State.hr + 1
}

-- Stuttering: hr' = hr
pred Stutter {
  State.hr' = State.hr
}

-- HC: HCini and always (HCnxt or stuttering)
fact HC {
  HCini
  always HCnxt
}

-- Run the specification
run example {} for 5 Int
check { always HCini }