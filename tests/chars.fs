char A . cr
char * emit cr

char A emit bl emit char B emit cr

: emit-star
    [char] * emit
;

emit-star cr

: emit-abc
    [char] A emit
    [char] B emit
    [char] C emit
;

emit-abc cr

: emit-a-b
    [char] A emit
    bl emit
    [char] B emit
    cr
;

emit-a-b
