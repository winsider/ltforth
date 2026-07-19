: countdown
    dup . cr
    1 -
    dup 0 >
    if
        recurse
    else
        drop
    then
;

5 countdown
