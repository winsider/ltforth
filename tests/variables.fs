variable counter
123 counter !
counter @ . cr

counter @ 1 + counter !
counter @ . cr

variable other
999 other !
other @ . cr
counter @ . cr

see counter

variable total

: inc-total
    total @ 1 + total !
;

0 total !
inc-total
inc-total
inc-total
total @ . cr

see total
