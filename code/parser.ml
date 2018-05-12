
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | STRING of (
# 1 "parser.mly"
       (string)
# 11 "parser.ml"
  )
    | SEMI
    | RPAREN
    | NEWLINE
    | LPAREN
    | EOF
    | COMMA
    | CAND of (
# 2 "parser.mly"
       (char)
# 22 "parser.ml"
  )
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState19
  | MenhirState17
  | MenhirState14
  | MenhirState0

let rec _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_reduce2 : _menhir_env -> (('ttv_tail * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 58 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, (v : 'tv_stmtone)), _, (ds : (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 64 "parser.ml"
    ))) = _menhir_stack in
    let _4 = () in
    let _2 = () in
    let _v : (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 71 "parser.ml"
    ) = 
# 17 "parser.mly"
                                       (v :: ds)
# 75 "parser.ml"
     in
    _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_separated_nonempty_list_SEMI_stmt_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_SEMI_stmt_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * _menhir_state * 'tv_stmt)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_SEMI_stmt_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * _menhir_state * 'tv_stmt)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_SEMI_stmt_) : 'tv_separated_nonempty_list_SEMI_stmt_) = _v in
        ((let (_menhir_stack, _menhir_s, (x : 'tv_stmt)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_SEMI_stmt_ = 
# 217 "/home/users/u5935541/.opam/4.06.0/lib/menhir/standard.mly"
    ( x :: xs )
# 96 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_SEMI_stmt_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv82)) : 'freshtv84)
    | MenhirState0 | MenhirState14 | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv101) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_SEMI_stmt_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv99) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((vs : 'tv_separated_nonempty_list_SEMI_stmt_) : 'tv_separated_nonempty_list_SEMI_stmt_) = _v in
        ((let _v : 'tv_stmtone = 
# 20 "parser.mly"
                                             (vs)
# 111 "parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv97) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_stmtone) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        match _menhir_s with
        | MenhirState0 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv89 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | NEWLINE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv85 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | EOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14
                | LPAREN ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState14
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14) : 'freshtv86)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv87 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)) : 'freshtv90)
        | MenhirState17 | MenhirState14 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv95 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | NEWLINE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv91 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | EOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState17
                | LPAREN ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState17
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17) : 'freshtv92)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv93 * _menhir_state * 'tv_stmtone) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)) : 'freshtv96)
        | _ ->
            _menhir_fail ()) : 'freshtv98)) : 'freshtv100)) : 'freshtv102)

and _menhir_goto_prog : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 179 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv69 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 189 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv65 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 199 "parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce2 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv66)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv67 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 210 "parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)) : 'freshtv70)
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv75 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 219 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv71 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 229 "parser.ml"
            )) = Obj.magic _menhir_stack in
            (_menhir_reduce2 _menhir_env (Obj.magic _menhir_stack) : 'freshtv72)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv73 * _menhir_state * 'tv_stmtone)) * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 239 "parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)) : 'freshtv76)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv79 * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 248 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv77 * _menhir_state * (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 254 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (_1 : (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 259 "parser.ml"
        ))) = _menhir_stack in
        Obj.magic _1) : 'freshtv78)) : 'freshtv80)
    | _ ->
        _menhir_fail ()

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * _menhir_state * 'tv_stmt)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * _menhir_state * 'tv_stmtone)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * _menhir_state * 'tv_stmtone)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv63) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv64)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CAND _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 2 "parser.mly"
       (char)
# 300 "parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv49 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 311 "parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | CAND _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv45 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 321 "parser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 2 "parser.mly"
       (char)
# 326 "parser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COMMA ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv41 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 337 "parser.ml"
                    ))) * (
# 2 "parser.mly"
       (char)
# 341 "parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | LPAREN ->
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : (((('freshtv37 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 351 "parser.ml"
                        ))) * (
# 2 "parser.mly"
       (char)
# 355 "parser.ml"
                        ))) = Obj.magic _menhir_stack in
                        ((let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        match _tok with
                        | STRING _v ->
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : ((((('freshtv33 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 365 "parser.ml"
                            ))) * (
# 2 "parser.mly"
       (char)
# 369 "parser.ml"
                            )))) = Obj.magic _menhir_stack in
                            let (_v : (
# 1 "parser.mly"
       (string)
# 374 "parser.ml"
                            )) = _v in
                            ((let _menhir_stack = (_menhir_stack, _v) in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            match _tok with
                            | COMMA ->
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : (((((('freshtv29 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 385 "parser.ml"
                                ))) * (
# 2 "parser.mly"
       (char)
# 389 "parser.ml"
                                )))) * (
# 1 "parser.mly"
       (string)
# 393 "parser.ml"
                                )) = Obj.magic _menhir_stack in
                                ((let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                match _tok with
                                | STRING _v ->
                                    let (_menhir_env : _menhir_env) = _menhir_env in
                                    let (_menhir_stack : ((((((('freshtv25 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 403 "parser.ml"
                                    ))) * (
# 2 "parser.mly"
       (char)
# 407 "parser.ml"
                                    )))) * (
# 1 "parser.mly"
       (string)
# 411 "parser.ml"
                                    ))) = Obj.magic _menhir_stack in
                                    let (_v : (
# 1 "parser.mly"
       (string)
# 416 "parser.ml"
                                    )) = _v in
                                    ((let _menhir_stack = (_menhir_stack, _v) in
                                    let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    match _tok with
                                    | RPAREN ->
                                        let (_menhir_env : _menhir_env) = _menhir_env in
                                        let (_menhir_stack : (((((((('freshtv21 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 427 "parser.ml"
                                        ))) * (
# 2 "parser.mly"
       (char)
# 431 "parser.ml"
                                        )))) * (
# 1 "parser.mly"
       (string)
# 435 "parser.ml"
                                        ))) * (
# 1 "parser.mly"
       (string)
# 439 "parser.ml"
                                        )) = Obj.magic _menhir_stack in
                                        ((let _menhir_env = _menhir_discard _menhir_env in
                                        let _tok = _menhir_env._menhir_token in
                                        match _tok with
                                        | RPAREN ->
                                            let (_menhir_env : _menhir_env) = _menhir_env in
                                            let (_menhir_stack : ((((((((('freshtv17 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 449 "parser.ml"
                                            ))) * (
# 2 "parser.mly"
       (char)
# 453 "parser.ml"
                                            )))) * (
# 1 "parser.mly"
       (string)
# 457 "parser.ml"
                                            ))) * (
# 1 "parser.mly"
       (string)
# 461 "parser.ml"
                                            ))) = Obj.magic _menhir_stack in
                                            ((let _menhir_env = _menhir_discard _menhir_env in
                                            let (_menhir_env : _menhir_env) = _menhir_env in
                                            let (_menhir_stack : ((((((((('freshtv15 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 468 "parser.ml"
                                            ))) * (
# 2 "parser.mly"
       (char)
# 472 "parser.ml"
                                            )))) * (
# 1 "parser.mly"
       (string)
# 476 "parser.ml"
                                            ))) * (
# 1 "parser.mly"
       (string)
# 480 "parser.ml"
                                            ))) = Obj.magic _menhir_stack in
                                            ((let (((((_menhir_stack, _menhir_s), (s : (
# 2 "parser.mly"
       (char)
# 485 "parser.ml"
                                            ))), (t : (
# 2 "parser.mly"
       (char)
# 489 "parser.ml"
                                            ))), (n : (
# 1 "parser.mly"
       (string)
# 493 "parser.ml"
                                            ))), (m : (
# 1 "parser.mly"
       (string)
# 497 "parser.ml"
                                            ))) = _menhir_stack in
                                            let _11 = () in
                                            let _10 = () in
                                            let _8 = () in
                                            let _6 = () in
                                            let _5 = () in
                                            let _3 = () in
                                            let _1 = () in
                                            let _v : 'tv_stmt = 
# 22 "parser.mly"
                                                                                                      ((s, t, (n, m)))
# 509 "parser.ml"
                                             in
                                            let (_menhir_env : _menhir_env) = _menhir_env in
                                            let (_menhir_stack : 'freshtv13) = _menhir_stack in
                                            let (_menhir_s : _menhir_state) = _menhir_s in
                                            let (_v : 'tv_stmt) = _v in
                                            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                                            let (_menhir_env : _menhir_env) = _menhir_env in
                                            let (_menhir_stack : 'freshtv11 * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
                                            ((assert (not _menhir_env._menhir_error);
                                            let _tok = _menhir_env._menhir_token in
                                            match _tok with
                                            | SEMI ->
                                                let (_menhir_env : _menhir_env) = _menhir_env in
                                                let (_menhir_stack : 'freshtv5 * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
                                                ((let _menhir_env = _menhir_discard _menhir_env in
                                                let _tok = _menhir_env._menhir_token in
                                                match _tok with
                                                | LPAREN ->
                                                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState19
                                                | _ ->
                                                    assert (not _menhir_env._menhir_error);
                                                    _menhir_env._menhir_error <- true;
                                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19) : 'freshtv6)
                                            | NEWLINE ->
                                                let (_menhir_env : _menhir_env) = _menhir_env in
                                                let (_menhir_stack : 'freshtv7 * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
                                                ((let (_menhir_stack, _menhir_s, (x : 'tv_stmt)) = _menhir_stack in
                                                let _v : 'tv_separated_nonempty_list_SEMI_stmt_ = 
# 215 "/home/users/u5935541/.opam/4.06.0/lib/menhir/standard.mly"
    ( [ x ] )
# 540 "parser.ml"
                                                 in
                                                _menhir_goto_separated_nonempty_list_SEMI_stmt_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv8)
                                            | _ ->
                                                assert (not _menhir_env._menhir_error);
                                                _menhir_env._menhir_error <- true;
                                                let (_menhir_env : _menhir_env) = _menhir_env in
                                                let (_menhir_stack : 'freshtv9 * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
                                                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)) : 'freshtv14)) : 'freshtv16)) : 'freshtv18)
                                        | _ ->
                                            assert (not _menhir_env._menhir_error);
                                            _menhir_env._menhir_error <- true;
                                            let (_menhir_env : _menhir_env) = _menhir_env in
                                            let (_menhir_stack : ((((((((('freshtv19 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 557 "parser.ml"
                                            ))) * (
# 2 "parser.mly"
       (char)
# 561 "parser.ml"
                                            )))) * (
# 1 "parser.mly"
       (string)
# 565 "parser.ml"
                                            ))) * (
# 1 "parser.mly"
       (string)
# 569 "parser.ml"
                                            ))) = Obj.magic _menhir_stack in
                                            ((let (((((_menhir_stack, _menhir_s), _), _), _), _) = _menhir_stack in
                                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv20)) : 'freshtv22)
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        let (_menhir_env : _menhir_env) = _menhir_env in
                                        let (_menhir_stack : (((((((('freshtv23 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 580 "parser.ml"
                                        ))) * (
# 2 "parser.mly"
       (char)
# 584 "parser.ml"
                                        )))) * (
# 1 "parser.mly"
       (string)
# 588 "parser.ml"
                                        ))) * (
# 1 "parser.mly"
       (string)
# 592 "parser.ml"
                                        )) = Obj.magic _menhir_stack in
                                        ((let (((((_menhir_stack, _menhir_s), _), _), _), _) = _menhir_stack in
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv24)) : 'freshtv26)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let (_menhir_env : _menhir_env) = _menhir_env in
                                    let (_menhir_stack : ((((((('freshtv27 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 603 "parser.ml"
                                    ))) * (
# 2 "parser.mly"
       (char)
# 607 "parser.ml"
                                    )))) * (
# 1 "parser.mly"
       (string)
# 611 "parser.ml"
                                    ))) = Obj.magic _menhir_stack in
                                    ((let ((((_menhir_stack, _menhir_s), _), _), _) = _menhir_stack in
                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv28)) : 'freshtv30)
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : (((((('freshtv31 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 622 "parser.ml"
                                ))) * (
# 2 "parser.mly"
       (char)
# 626 "parser.ml"
                                )))) * (
# 1 "parser.mly"
       (string)
# 630 "parser.ml"
                                )) = Obj.magic _menhir_stack in
                                ((let ((((_menhir_stack, _menhir_s), _), _), _) = _menhir_stack in
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)) : 'freshtv34)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : ((((('freshtv35 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 641 "parser.ml"
                            ))) * (
# 2 "parser.mly"
       (char)
# 645 "parser.ml"
                            )))) = Obj.magic _menhir_stack in
                            ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv36)) : 'freshtv38)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : (((('freshtv39 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 656 "parser.ml"
                        ))) * (
# 2 "parser.mly"
       (char)
# 660 "parser.ml"
                        ))) = Obj.magic _menhir_stack in
                        ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)) : 'freshtv42)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv43 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 671 "parser.ml"
                    ))) * (
# 2 "parser.mly"
       (char)
# 675 "parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)) : 'freshtv46)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv47 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 686 "parser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)) : 'freshtv50)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv51 * _menhir_state) * (
# 2 "parser.mly"
       (char)
# 697 "parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)) : 'freshtv54)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv55 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)

and _menhir_reduce1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _1 = () in
    let _v : (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 715 "parser.ml"
    ) = 
# 16 "parser.mly"
       ([])
# 719 "parser.ml"
     in
    _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 11 "parser.mly"
       ((char * char * (string * string)) list list)
# 738 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv3) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        (_menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) _menhir_s : 'freshtv2)
    | LPAREN ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv4))

# 219 "/home/users/u5935541/.opam/4.06.0/lib/menhir/standard.mly"
  


# 773 "parser.ml"
