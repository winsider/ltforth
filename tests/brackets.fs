: test
    1 .
    [ 2 . cr ]
    3 .
    cr
;

test

: a
    ." compiling-a" cr
;

: b
    ." before" cr
    [ a ]
    ." after" cr
;

b
