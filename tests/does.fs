: constant2
    create ,
    does> @
;

123 constant2 foo
foo . cr

456 constant2 bar
bar . cr
foo . cr

see constant2
see foo

: array3
    create , , ,
    does> swap cells + @
;

10 20 30 array3 nums

0 nums . cr
1 nums . cr
2 nums . cr

see nums
