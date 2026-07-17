: hello
    ." Hello" cr
;

' hello execute

: star
    [char] * emit
;

' star execute cr

123 constant answer
' answer execute . cr

variable counter
456 counter !
' counter execute @ . cr

: constant2
    create ,
    does> @
;

789 constant2 foo
' foo execute . cr
