:- [test_decl].
:- use_module(signature_decl).

:- type system:read_mode ---> read.

:- pred system:open(+any, +read_mode, -input_stream) is det.
:- pred system:read(+input_stream, -any) is det.
:- pred system:write(+output_stream, -any) is det.
