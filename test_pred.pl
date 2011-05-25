:- [test_decl].
:- use_module(signature_decl).

:- type system:read_mode ---> read.
:- type system:write_mode ---> write ; append ; update.

:- pred system:open(+any, +read_mode, -input_stream) is det.
:- pred system:open(+any, +write_mode, -output_stream) is det.
:- pred system:read(+input_stream, -any) is det.
:- pred system:write(+output_stream, -any) is det.
