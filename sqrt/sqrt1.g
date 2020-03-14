@rnd = float< ieee_32, ne >;
x = rnd(a_);
{a in [1,4] /\ b in [0,1] ->
  rnd (
    rnd( rnd ((sqrt(a) * x + (1 - x) * a) / 2) +
       rnd (a / rnd ((sqrt(a) * x + (1 - x) * a) / 2))) / 2) -
    (rnd ((sqrt(a) * x + (1 - x) * a) / 2) +
      a / rnd ((sqrt(a) * x + (1 - x) * a) / 2)) / 2 in ?}
