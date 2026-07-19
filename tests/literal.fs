: answer
    [ 40 2 + ] literal
;

answer . cr

: stars
    [ 5 ] literal 0 do
        [char] * emit
    loop
    cr
;

stars
