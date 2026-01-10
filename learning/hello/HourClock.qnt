module HourClock {
  var hr: int

  action init = {
    nondet init_hr = 1.to(12).oneOf()
    hr' = init_hr
  }

  action step = {
    hr' = if (hr != 12) hr + 1 else 1
  }

  val invariant = hr.in(1.to(12))
}