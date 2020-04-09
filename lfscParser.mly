%{
(* This translator is adapted from SMTCoq's LFSC translator *)

open Lexing
open Format

let concat_sp_sep_2 a b = "("^a^" "^b^")"
let concat_sp_sep_3 a b c = "("^a^" "^b^" "^c^")"
let concat_sp_sep_4 a b c d = "("^a^" "^b^" "^c^" "^d^")"
let concat_sp_sep_5 a b c d e = "("^a^" "^b^" "^c^" "^d^" "^e^")"
let concat_sp_sep_6 a b c d e f = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^")"
let concat_sp_sep_7 a b c d e f g = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^" "^g^")"
let concat_sp_sep_8 a b c d e f g h = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^" "^g^" "^h^")"
%}

%token <string> IDENT
%token <string> ANYTHING
%token <int> INT
%token LPAREN RPAREN EOF LAMBDA BIGLAMBDA COLON CHECK HOLE VAR HOLDS CLC CLN POS NEG
%token SATLEM_SIMPLIFY SATLEM RRES QRES CONCAT_CL CLR CNFN CNFC CNF_HOLDS CNFN_PROOF CNFC_PROOF
%token TH_HOLDS TRUE FALSE NOT AND OR IMPL TYPE
%token IFF XOR IFTE TERM EQUALS ITE LET FLET BOOL P_APP T_TRUE T_FALSE T_T_NEQ_F PRED_EQ_T PRED_EQ_F F_TO_B
%token TRUE_PREDS_EQUAL FALSE_PREDS_EQUAL PRED_REFL_POS PRED_REFL_NEG PRED_NOT_IFF_F PRED_NOT_IFF_F_2
%token PRED_NOT_IFF_T PRED_NOT_IFF_T_2 PRED_IFF_F PRED_IFF_F_2 PRED_IFF_T PRED_IFF_T_2
%token DECL_ATOM DECL_BVATOM CLAUSIFY_FORM CLAUSIFY_FORM_NOT CLAUSIFY_FALSE TH_LET_PF
%token IFF_SYMM CONTRAD TRUTH NOT_NOT_INTRO NOT_NOT_ELIM OR_ELIM_1 OR_ELIM_2 NOT_OR_ELIM AND_ELIM_1 AND_ELIM_2
%token NOT_AND_ELIM IMPL_INTRO IMPL_ELIM NOT_IMPL_ELIM IFF_ELIM_1 IFF_ELIM_2 NOT_IFF_ELIM XOR_ELIM_1 XOR_ELIM_2
%token NOT_XOR_ELIM  ITE_ELIM_1 ITE_ELIM_2 ITE_ELIM_3 NOT_ITE_ELIM_1 NOT_ITE_ELIM_2
%token NOT_ITE_ELIM_3 AST ASF BV_AST BV_ASF TRUST TRUST_F ARROW APPLY REFL SYMM TRANS NEGSYMM NEGTRANS1 NEGTRANS2 CONG
%token ARRAY SORT READ WRITE ROW1 ROW NEGATIVEROW EXT VARBV BITVEC AVARBV TRUSTBAD
%token ABV BVC BVN B0 B1 BVDISEQ BVAND BVOR BVXOR BVNAND BVNOR BVXNOR BVMUL BVADD BVSUB BVUDIV BVUREM
%token BVSDIV BVSREM BVSMOD BVSHL BVLSHR BVASHR BVCONCAT BVNEG BVNOT BVLROTATE BVRROTATE BVCOMP
%token BVEXTRACT BVZEROEXT BVSIGNEXT BVREPEAT

%token HASH_SEMI SC PROGRAM AT MPQ MPZ KIND PI

%start command
%type <unit> command
%%

lit:
  | LPAREN POS IDENT RPAREN
    { concat_sp_sep_2 "lit.pos" ($3) }
  | LPAREN NEG IDENT RPAREN
    { concat_sp_sep_2 "lit.neg" ($3) }
;

clause:
  | CLN { "[]" }
  | LPAREN CLC lit clause RPAREN
    { ($3^" :: "^$4) }
  | LPAREN CONCAT_CL clause clause RPAREN
    { ("concat_cl "^$3^" "^$4) }
  | LPAREN CLR lit clause RPAREN
    { ("clr "^$3^" "^$4) }
  | HOLE { "" }
;

cnf:
  | CNFN { "[]" }
  | LPAREN CNFC clause cnf RPAREN
    { ("("^$3^") :: ("^$4^")") }
  | HOLE { "" }
;

fixed_sort:
  | BOOL { "Bool" }
  | LPAREN ARRAY sort sort RPAREN 
    { (concat_sp_sep_3 "Array" $3 $4) }
  | LPAREN BITVEC INT RPAREN
    { (concat_sp_sep_3 "_" "BitVec" (string_of_int($3))) }
  | IDENT { $1 }
;

arrow_sort_rec:
  | LPAREN ARROW fixed_sort arrow_sort_rec RPAREN
    { (" "^$3^$4) }
  | fixed_sort { (") "^$1) }
;

arrow_sort_init:
  | LPAREN ARROW fixed_sort arrow_sort_rec RPAREN
    { ("("^$3^$4) }
;

sort:
  | fixed_sort { $1 }
  | arrow_sort_init { $1 }
  | HOLE { "" }
;

apply_rec:
  | LPAREN APPLY sort sort apply_rec sorted_term RPAREN
    { ($5^" "^$6) }
  | sorted_term_without_apply { $1 }
;

apply_init:
  | LPAREN APPLY sort sort apply_rec sorted_term RPAREN
    { ("("^$5^" "^$6^")")}
;

bvconst:
  | LPAREN BVC B0 bvconst RPAREN { ("0"^$4) }
  | LPAREN BVC B1 bvconst RPAREN { ("1"^$4) }
  | BVN { "" }
;

int_or_hole:
  | INT { "" }
  | HOLE { "" }
;

sorted_bv_term:
  | LPAREN AVARBV INT IDENT RPAREN
    { $4 }
  | LPAREN ABV INT bvconst RPAREN
    { ("#b"^$4) }
  | LPAREN BVAND INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvand" $4 $5) }
  | LPAREN BVOR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvor" $4 $5) }
  | LPAREN BVXOR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvxor" $4 $5) }
  | LPAREN BVNAND INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvnand" $4 $5) }
  | LPAREN BVNOR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvnor" $4 $5) }
  | LPAREN BVXNOR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvxnor" $4 $5) }
  | LPAREN BVMUL INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvmul" $4 $5) }
  | LPAREN BVADD INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvadd" $4 $5) }
  | LPAREN BVSUB INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvsub" $4 $5) }
  | LPAREN BVUDIV INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvudiv" $4 $5) }
  | LPAREN BVUREM INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvurem" $4 $5) }
  | LPAREN BVSDIV INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvsdiv" $4 $5) }
  | LPAREN BVSREM INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvsrem" $4 $5) }
  | LPAREN BVSMOD INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvsmod" $4 $5) }
  | LPAREN BVSHL INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvshl" $4 $5) }
  | LPAREN BVLSHR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvlshr" $4 $5) }
  | LPAREN BVASHR INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvashr" $4 $5) }
  | LPAREN BVCONCAT INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "concat" $4 $5) }
  | LPAREN BVNEG INT sorted_bv_term RPAREN
    { (concat_sp_sep_2 "bvneg" $4) }
  | LPAREN BVNOT INT sorted_bv_term RPAREN
    { (concat_sp_sep_2 "bvnot" $4) }
  | LPAREN BVLROTATE INT sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_3 "_" "rotate_left" (string_of_int $3)) 
                       $4) }
  | LPAREN BVRROTATE INT sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_3 "_" "rotate_right" (string_of_int $3)) 
                       $4) }
  | LPAREN BVCOMP INT sorted_bv_term sorted_bv_term RPAREN
    { (concat_sp_sep_3 "bvcomp" $4 $5) }
  | LPAREN BVEXTRACT INT INT INT INT sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_4 "_" "extract" (string_of_int $4) (string_of_int $5))
                       $7) }
  | LPAREN BVZEROEXT INT INT int_or_hole sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_3 "_" "zero_extend" (string_of_int $4))
                       $6) }
  | LPAREN BVSIGNEXT INT INT int_or_hole sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_3 "_" "sign_extend" (string_of_int $4))
                       $6) }
  | LPAREN BVREPEAT INT INT int_or_hole sorted_bv_term RPAREN
    { (concat_sp_sep_2 (concat_sp_sep_3 "_" "repeat" (string_of_int $4))
                       $6) }
;

sorted_term_without_apply:
  | LPAREN ITE sort formula sorted_term sorted_term RPAREN
    { concat_sp_sep_4 "ite" $4 $5 $6 }
  | T_TRUE { "true" }
  | T_FALSE { "false" }
  | LPAREN F_TO_B formula RPAREN
    { $3 }
  | LPAREN WRITE sort sort RPAREN 
    { "store" }
  | LPAREN READ sort sort RPAREN 
    { "select" }
  | sorted_bv_term { $1 }  
  | IDENT { ($1) }
  | HOLE 
    { ("IFUCKEDUP!-sorted_term->HOLE") }
;

sorted_term:
  | LPAREN ITE sort formula sorted_term sorted_term RPAREN
    { concat_sp_sep_4 "ite" $4 $5 $6 }
  | T_TRUE { "true" }
  | T_FALSE { "false" }
  | LPAREN F_TO_B formula RPAREN
    { $3 }
  | apply_init { $1 }
  | LPAREN WRITE sort sort RPAREN 
    { "store" }
  | LPAREN READ sort sort RPAREN 
    { "select" }   
  | sorted_bv_term { $1 }   
  | IDENT { ($1) }
  | HOLE 
    { ("IFUCKEDUP!-sorted_term->HOLE") }
;

formula:
  | TRUE { "true" }
  | FALSE { "false" }
  | LPAREN NOT formula RPAREN 
    { (concat_sp_sep_2 "not" $3) }
  | LPAREN AND formula formula RPAREN
    { (concat_sp_sep_3 "and" $3 $4) }
  | LPAREN OR formula formula RPAREN
    { (concat_sp_sep_3 "or" $3 $4) }
  | LPAREN IMPL formula formula RPAREN
    { (concat_sp_sep_3 "=>" $3 $4) }
  | LPAREN IFF formula formula RPAREN
    { (concat_sp_sep_3 "=" $3 $4) }
  | LPAREN XOR formula formula RPAREN
    { (concat_sp_sep_3 "xor" $3 $4) }
  | LPAREN IFTE formula formula formula RPAREN
    { (concat_sp_sep_4 "ite" $3 $4 $5) }
  | LPAREN EQUALS sort sorted_term sorted_term RPAREN
    { (concat_sp_sep_3 "=" $4 $5) }
  | LET sort sorted_term LPAREN LAMBDA IDENT formula RPAREN
    { "IFUCKEDUP!-formula->LET" }
  | FLET formula LPAREN LAMBDA IDENT formula RPAREN
    { "IFUCKEDUP!-formula->FLET" }
  | LPAREN P_APP sorted_term RPAREN { $3 }
  | HOLE { "" }
;

holds_term:
  | LPAREN HOLDS clause RPAREN
    { ("holds ("^$3^")") }
  | LPAREN CNF_HOLDS cnf RPAREN
    { ("cnf_holds ("^$3^")") }
  | LPAREN TH_HOLDS formula RPAREN
    { ($3) }
  | IDENT { $1 }
;

proof_term:
  | LPAREN SATLEM clause clause proof_term proof_term RPAREN
    { "(satlem "^$3^$4^$5^" "^$6^")" }
  | LPAREN SATLEM_SIMPLIFY clause clause clause proof_term proof_term RPAREN
    { "(satlem_simplify "^$3^$4^$5^$6^" \n"^" _ "^$7^")" }
  | LPAREN RRES clause clause proof_term proof_term IDENT RPAREN
    { "(R "^$3^$4^$5^" "^$6^" "^$7^")" }
  | LPAREN QRES clause clause proof_term proof_term IDENT RPAREN
    { "(Q "^$3^$4^$5^" "^$6^" "^$7^")" }
  | LPAREN LAMBDA IDENT proof_term RPAREN { "(fun "^$3^",\n   "^$4^")" }
  | CNFN_PROOF { "cnfn_proof" }
  | LPAREN CNFC_PROOF clause clause cnf proof_term proof_term RPAREN
    { "(cnfc_proof \n"^$3^$4^$5^" "^$6^" "^$7^")" }
  | T_T_NEQ_F { "t_t_neq_f" }
  | LPAREN PRED_EQ_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_eq_t" $3 $4 }
  | LPAREN PRED_EQ_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_eq_f" $3 $4 }
  | LPAREN TRUE_PREDS_EQUAL sorted_term sorted_term holds_term holds_term RPAREN
    { concat_sp_sep_5 "true_preds_equal" $3 $4 $5 $6 }
  | LPAREN FALSE_PREDS_EQUAL sorted_term sorted_term holds_term holds_term RPAREN
    { concat_sp_sep_5 "false_preds_equal" $3 $4 $5 $6 }
  | LPAREN PRED_REFL_POS sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_refl_pos" $3 $4 }
  | LPAREN PRED_REFL_NEG sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_refl_neg" $3 $4 }
  | LPAREN PRED_NOT_IFF_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_f" $3 $4 }
  | LPAREN PRED_NOT_IFF_F_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_f_2" $3 $4 }
  | LPAREN PRED_NOT_IFF_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_t" $3 $4 }
  | LPAREN PRED_NOT_IFF_T_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_t_2" $3 $4 }
  | LPAREN PRED_IFF_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_f" $3 $4 }
  | LPAREN PRED_IFF_F_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_f_2" $3 $4 }
  | LPAREN PRED_IFF_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_t" $3 $4 }
  | LPAREN PRED_IFF_T_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_t_2" $3 $4 }
  | LPAREN DECL_ATOM formula proof_term RPAREN
    { concat_sp_sep_3 "decl_atom" $3 $4 }
  | LPAREN DECL_BVATOM formula proof_term RPAREN
    { concat_sp_sep_3 "decl_bv_atom" $3 $4 }
  | LPAREN CLAUSIFY_FORM formula proof_term proof_term proof_term RPAREN
    { concat_sp_sep_5 "clausify_form" $3 $4 $5 $6 }
  | LPAREN CLAUSIFY_FORM_NOT formula proof_term proof_term proof_term RPAREN
    { concat_sp_sep_5 "clausify_form_not" $3 $4 $5 $6 }
  | LPAREN CLAUSIFY_FALSE proof_term RPAREN
    { concat_sp_sep_2 "clausify_false" $3 }
  | LPAREN TH_LET_PF formula proof_term proof_term RPAREN
    { concat_sp_sep_4 "th_let_pf" $3 $4 $5 }
  | LPAREN IFF_SYMM formula RPAREN
    { concat_sp_sep_2 "iff_symm" $3 }
  | LPAREN CONTRAD formula proof_term proof_term RPAREN
    { concat_sp_sep_4 "contra" $3 $4 $5 }
  | TRUTH { "truth" }
  | LPAREN NOT_NOT_INTRO formula proof_term RPAREN
    { concat_sp_sep_3 "not_not_intro" $3 $4 }
  | LPAREN NOT_NOT_ELIM formula proof_term RPAREN
    { concat_sp_sep_3 "not_not_elim" $3 $4 }
  | LPAREN OR_ELIM_1 formula formula proof_term proof_term RPAREN
    { concat_sp_sep_3 "or_elim_1" $5 $6 }
  | LPAREN OR_ELIM_2 formula formula proof_term proof_term RPAREN
    { concat_sp_sep_3 "or_elim_2" $5 $6 }
  | LPAREN NOT_OR_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_or_elim" $5 }
  | LPAREN AND_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "and_elim_1" $5 }
  | LPAREN AND_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "and_elim_2" $5 }
  | LPAREN NOT_AND_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_and_elim" $5 }
  | LPAREN IMPL_INTRO formula formula proof_term RPAREN
    { concat_sp_sep_2 "impl_intro" $5 }
  | LPAREN IMPL_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "impl_elim" $5 }
  | LPAREN NOT_IMPL_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_impl_elim" $5 }
  | LPAREN IFF_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "iff_elim_1" $5 }
  | LPAREN IFF_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "iff_elim_2" $5 }
  | LPAREN NOT_IFF_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_iff_elim" $5 }
  | LPAREN XOR_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "xor_elim_1" $5 }
  | LPAREN XOR_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "xor_elim_2" $5 }
  | LPAREN NOT_XOR_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_xor_elim" $5 }
  | LPAREN ITE_ELIM_1 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_1" $6 }
  | LPAREN ITE_ELIM_2 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_2" $6 }
  | LPAREN ITE_ELIM_3 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_3" $6 }
  | LPAREN NOT_ITE_ELIM_1 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_1" $6 }
  | LPAREN NOT_ITE_ELIM_2 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_2" $6 }
  | LPAREN NOT_ITE_ELIM_3 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_3" $6 }
  | LPAREN AST proof_term formula clause proof_term proof_term RPAREN
    { concat_sp_sep_6 "ast" $3 $4 $5 $6 $7 }
  | LPAREN ASF proof_term formula clause proof_term proof_term RPAREN
    { concat_sp_sep_6 "asf" $3 $4 $5 $6 $7 }
  | LPAREN BV_ASF proof_term proof_term formula clause proof_term proof_term proof_term RPAREN
    { concat_sp_sep_8 "bv_asf" $3 $4 $5 $6 $7 $8 $9 }
  | LPAREN BV_AST proof_term proof_term formula clause proof_term proof_term proof_term RPAREN
    { concat_sp_sep_8 "bv_ast" $3 $4 $5 $6 $7 $8 $9 }
  | TRUST { "trust" }
  | LPAREN TRUST_F formula RPAREN
    { concat_sp_sep_2 "trust_f" $3 }
  | LPAREN REFL sort sorted_term RPAREN
    { concat_sp_sep_2 "refl" $4 }
  | LPAREN SYMM sort sorted_term sorted_term proof_term RPAREN
    { concat_sp_sep_2 "symm" $6 }
  | LPAREN TRANS sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "trans" $7 $8 }
  | LPAREN NEGSYMM sort sorted_term sorted_term proof_term RPAREN
    { concat_sp_sep_2 "negsymm" $6 }
  | LPAREN NEGTRANS1 sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "negtrans1" $7 $8 }
  | LPAREN NEGTRANS2 sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "negtrans2" $7 $8 }
  | LPAREN CONG sort sort sorted_term sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "cong" $9 $10 }
  /*Producing empty output from here on since we don't need output for proof body*/
  | LPAREN ROW1 sort sort sorted_term sorted_term sorted_term RPAREN
    { "" }
  | LPAREN ROW sort sort sorted_term sorted_term sorted_term sorted_term proof_term RPAREN
    { "" }
  | LPAREN NEGATIVEROW sort sort sorted_term sorted_term sorted_term sorted_term proof_term RPAREN
    { "" }
  | LPAREN EXT sort sort sorted_term sorted_term proof_term RPAREN
    { "" }
  | TRUSTBAD
    { "" }
  | LPAREN BVDISEQ INT bvconst bvconst RPAREN
    { "" }
  | HOLE { "" }
  | IDENT { (" "^$1^" ") }
;

typed_var:
  | IDENT VAR 
    { "IFUCKEDUP!-typed_var->IDENT VAR" }
  | IDENT VARBV
    { (concat_sp_sep_4 "declare-fun" $1 "()" "(_ BitVec )") }
  | IDENT LPAREN TERM fixed_sort RPAREN
    { (concat_sp_sep_4 "declare-fun" $1 "()" $4) }
  | IDENT LPAREN TERM arrow_sort_init RPAREN 
    { (concat_sp_sep_3 "declare-fun" $1 $4) }
  | IDENT SORT 
    { (concat_sp_sep_3 "declare-sort" $1 "0") }
  | IDENT holds_term 
    { (concat_sp_sep_2 "assert" $2) }
;

/* My attempts to ignore the proof body:
holds_anything_term:
  | LPAREN ANYTHING RPAREN
    { "" }
;

proof_anything_term:
  | LPAREN ANYTHING RPAREN
    { "" }
;
*/

term:
  | LPAREN COLON holds_term proof_term RPAREN
    { "" }
  | LPAREN BIGLAMBDA typed_var term RPAREN
    { $3^"\n"^$4 }
;

check_command:
  | LPAREN CHECK term RPAREN
    { print_string 
      ("(set-logic ALL_SUPPORTED)\n"
        ^$3^"(check-sat)\n") }
;

command:
  | check_command EOF { $1 }
;