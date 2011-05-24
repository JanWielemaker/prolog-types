:- [test_decl].
:- use_module(signature_decl).

:- pred open(+any, +read_mode, -input_stream) is det.
:- pred read(+input_stream, -any) is det.
:- pred write(+output_stream, -any) is det.
