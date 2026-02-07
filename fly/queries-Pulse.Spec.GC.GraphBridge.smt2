; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)
(set-option :smt.random-seed 0)


(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-datatypes () ((Universe 
(Univ (ulevel Int)))))
(define-fun imax ((i Int) (j Int)) Int 
(ite (<= i 0) j 
(ite (<= j 0) i 
(ite (<= i j) j i)))) 
(define-fun U_zero () Universe (Univ 0))
(define-fun U_succ ((u Universe)) Universe
(Univ (+ (ulevel u) 1)))
(declare-fun U_max (Universe Universe) Universe) 
(assert (forall ((u1 Universe) (u2 Universe)) 
(! (= (U_max u1 u2)
(Univ (imax (ulevel u1) (ulevel u2))))
:pattern ((U_max u1 u2)))))
(assert (forall ((u Universe)) (>= (ulevel u) 0)))
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

                ;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
;;no-hoist
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b) b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(assert (forall ((x Term) (y Term) (z Term))
(! (implies (and (Prec x y) (Prec y z)) (Prec x z))
:pattern ((Prec x z) (Prec x y)))))
(assert (forall ((x Term) (y Term))
(implies (Prec x y)
(not (Prec y x)))))
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Universe Universe Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
(define-fun Unreachable () Bool false); <start constructor FString_const>
; Constructor
(declare-fun FString_const (Int) FString)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 0 (FString_constr_id (FString_const @u0)))
    :pattern ((FString_const @u0))
    :qid constructor_distinct_FString_const))
  :named constructor_distinct_FString_const))
; Projector
(declare-fun FString_const_proj_0 (FString) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (FString_const_proj_0 (FString_const @u0)) @u0)
    :pattern ((FString_const @u0))
    :qid projection_inverse_FString_const_proj_0))
  :named projection_inverse_FString_const_proj_0))
; Discriminator definition
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0) 0) (= __@u0 (FString_const (FString_const_proj_0 __@u0)))))
; </end constructor FString_const>
; <start constructor Tm_type>
; Constructor
(declare-fun Tm_type (Universe) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= 2 (Term_constr_id (Tm_type @u0)))
    :pattern ((Tm_type @u0))
    :qid constructor_distinct_Tm_type))
  :named constructor_distinct_Tm_type))
; Projector
(declare-fun Tm_type_0 (Term) Universe)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Universe))
   (! (= (Tm_type_0 (Tm_type @u0)) @u0) :pattern ((Tm_type @u0)) :qid projection_inverse_Tm_type_0))
  :named projection_inverse_Tm_type_0))
; Discriminator definition
(define-fun is-Tm_type ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 2) (= __@x0 (Tm_type (Tm_type_0 __@x0)))))
; </end constructor Tm_type>
; <start constructor Tm_arrow>
; Constructor
(declare-fun Tm_arrow (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 3 (Term_constr_id (Tm_arrow @u0)))
    :pattern ((Tm_arrow @u0))
    :qid constructor_distinct_Tm_arrow))
  :named constructor_distinct_Tm_arrow))
; Projector
(declare-fun Tm_arrow_id (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0)
    :pattern ((Tm_arrow @u0))
    :qid projection_inverse_Tm_arrow_id))
  :named projection_inverse_Tm_arrow_id))
; Discriminator definition
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 3) (= __@x0 (Tm_arrow (Tm_arrow_id __@x0)))))
; </end constructor Tm_arrow>
; <start constructor Tm_unit>
; Constructor
(declare-fun Tm_unit () Term)
; Constructor distinct
;;; Fact-ids: 
(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))
; Discriminator definition
(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))
; </end constructor Tm_unit>
; <start constructor BoxInt>
; Constructor
(declare-fun BoxInt (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 7 (Term_constr_id (BoxInt @u0))) :pattern ((BoxInt @u0)) :qid constructor_distinct_BoxInt))
  :named constructor_distinct_BoxInt))
; Projector
(declare-fun BoxInt_proj_0 (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0)
    :pattern ((BoxInt @u0))
    :qid projection_inverse_BoxInt_proj_0))
  :named projection_inverse_BoxInt_proj_0))
; Discriminator definition
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))
; </end constructor BoxInt>
; <start constructor BoxBool>
; Constructor
(declare-fun BoxBool (Bool) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= 8 (Term_constr_id (BoxBool @u0)))
    :pattern ((BoxBool @u0))
    :qid constructor_distinct_BoxBool))
  :named constructor_distinct_BoxBool))
; Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0)
    :pattern ((BoxBool @u0))
    :qid projection_inverse_BoxBool_proj_0))
  :named projection_inverse_BoxBool_proj_0))
; Discriminator definition
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))
; </end constructor BoxBool>
; <start constructor BoxString>
; Constructor
(declare-fun BoxString (FString) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= 9 (Term_constr_id (BoxString @u0)))
    :pattern ((BoxString @u0))
    :qid constructor_distinct_BoxString))
  :named constructor_distinct_BoxString))
; Projector
(declare-fun BoxString_proj_0 (Term) FString)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= (BoxString_proj_0 (BoxString @u0)) @u0)
    :pattern ((BoxString @u0))
    :qid projection_inverse_BoxString_proj_0))
  :named projection_inverse_BoxString_proj_0))
; Discriminator definition
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 9) (= __@x0 (BoxString (BoxString_proj_0 __@x0)))))
; </end constructor BoxString>
; <start constructor BoxReal>
; Constructor
(declare-fun BoxReal (Real) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= 10 (Term_constr_id (BoxReal @u0)))
    :pattern ((BoxReal @u0))
    :qid constructor_distinct_BoxReal))
  :named constructor_distinct_BoxReal))
; Projector
(declare-fun BoxReal_proj_0 (Term) Real)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= (BoxReal_proj_0 (BoxReal @u0)) @u0)
    :pattern ((BoxReal @u0))
    :qid projection_inverse_BoxReal_proj_0))
  :named projection_inverse_BoxReal_proj_0))
; Discriminator definition
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 10) (= __@x0 (BoxReal (BoxReal_proj_0 __@x0)))))
; </end constructor BoxReal>
; <start constructor LexCons>
; Constructor
(declare-fun LexCons (Term Term Term) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= 11 (Term_constr_id (LexCons @x0 @x1 @x2)))
    :pattern ((LexCons @x0 @x1 @x2))
    :qid constructor_distinct_LexCons))
  :named constructor_distinct_LexCons))
; Projector
(declare-fun LexCons_0 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_0 (LexCons @x0 @x1 @x2)) @x0)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_0))
  :named projection_inverse_LexCons_0))
; Projector
(declare-fun LexCons_1 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_1 (LexCons @x0 @x1 @x2)) @x1)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_1))
  :named projection_inverse_LexCons_1))
; Projector
(declare-fun LexCons_2 (Term) Term)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (LexCons_2 (LexCons @x0 @x1 @x2)) @x2)
    :pattern ((LexCons @x0 @x1 @x2))
    :qid projection_inverse_LexCons_2))
  :named projection_inverse_LexCons_2))
; Discriminator definition
(define-fun is-LexCons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 11)
  (= __@x0 (LexCons (LexCons_0 __@x0) (LexCons_1 __@x0) (LexCons_2 __@x0)))))
; </end constructor LexCons>
(declare-fun Prims.precedes@tok (Universe Universe) Term)
(assert
(forall ((u0 Universe) (u1 Universe) (@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)
(Prims.precedes u0 u1 @x0 @x1 @x2 @x3))
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (Prims.precedes@tok u0 u1) @x0) @x1) @x2) @x3)))))

(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(declare-fun Prims.lex_t () Term)
(declare-fun LexTop () Term)
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))
(or (Valid (Prims.precedes u0 u1 t1 t2 x1 y1))
(and (= x1 y1)
(Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t x2 y2)))))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes u0 u1 t1 t2 e1 e2))
(Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes u0 u1 t1 t2 e1 e2))))
(assert (forall ((u0 Universe) (u1 Universe) (t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)) 
(Prec t1 t2))
:pattern ((Prims.precedes u0 u1 Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((e Term) (t Term))
(! (implies (HasType e t)
(Valid t))
:pattern ((HasType e t)
(Valid t))
:qid __prelude_valid_intro)))
(assert (forall ((u Universe) (t Term))
(! (iff (HasType (Tm_type u) t)
(= t (Tm_type (U_succ u))))
:pattern ((HasType (Tm_type u) t)))))

(push) ;; push{1
; Constructor
(declare-fun FStar.Pervasives.Native.Mktuple2 (Universe Universe Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@0 (Term) Universe)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@1 (Term) Universe)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@_1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@_2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2_@_b (Term) Term)
; Constructor
(declare-fun FStar.Pervasives.Native.tuple2 (Universe Universe Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple2@tok (Universe Universe) Term)
(declare-fun FStar.Seq.Base.append (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.cons (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.create (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.empty (Universe Term) Term)
(declare-fun FStar.Seq.Base.length (Universe Term Term) Term)
(declare-fun FStar.Seq.Base.seq (Universe Term) Term)
(declare-fun FStar.UInt.fits (Term Term) Term)
(declare-fun FStar.UInt.max_int (Term) Term)
(declare-fun FStar.UInt.min_int (Term) Term)
(declare-fun FStar.UInt.size (Term Term) Term)
(declare-fun FStar.UInt.uint_t (Term) Term)
(declare-fun FStar.UInt64.add (Term Term) Term)
(declare-fun FStar.UInt64.mul (Term Term) Term)
(declare-fun FStar.UInt64.sub (Term Term) Term)
(declare-fun FStar.UInt64.t (Dummy_sort) Term)
(declare-fun FStar.UInt64.uint_to_t (Term) Term)
(declare-fun FStar.UInt64.v (Term) Term)
(declare-fun FStar.UInt8.t (Dummy_sort) Term)
; Constructor
(declare-fun Prims.T () Term)
; data constructor proxy: Prims.T
(declare-fun Prims.T@tok () Term)
(declare-fun Prims.__cache_version_number__ () Term)
(declare-fun Prims.b2t (Term) Term)
(declare-fun Prims.bool () Term)
(declare-fun Prims.eqtype () Term)
(declare-fun Prims.hasEq (Universe Term) Term)
(declare-fun Prims.int () Term)
(declare-fun Prims.l_True () Term)
(declare-fun Prims.logical () Term)
(declare-fun Prims.nat () Term)
(declare-fun Prims.op_Addition (Term Term) Term)
(declare-fun Prims.op_AmpAmp (Term Term) Term)
(declare-fun Prims.op_Equality (Term Term Term) Term)
(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(declare-fun Prims.op_LessThan (Term Term) Term)
(declare-fun Prims.op_LessThanOrEqual (Term Term) Term)
(declare-fun Prims.op_Modulus (Term Term) Term)
(declare-fun Prims.op_Multiply (Term Term) Term)
(declare-fun Prims.op_Subtraction (Term Term) Term)
(declare-fun Prims.op_disEquality (Term Term Term) Term)
(declare-fun Prims.pos () Term)
(declare-fun Prims.pow2 (Term) Term)
; Fuel-instrumented function name
(declare-fun Prims.pow2.fuel_instrumented (Fuel Term) Term)
(declare-fun Prims.prop () Term)
(declare-fun Prims.pure_post (Universe Term) Term)
(declare-fun Prims.pure_post_ (Universe Universe Term Term) Term)
(declare-fun Prims.squash (Universe Term) Term)
(declare-fun Prims.subtype_of (Universe Universe Term Term) Term)
; Constructor
(declare-fun Prims.trivial () Term)
(declare-fun Prims.unit () Term)
(declare-fun Pulse.Spec.GC.Base.heap () Term)
(declare-fun Pulse.Spec.GC.Base.heap_size (Dummy_sort) Term)
(declare-fun Pulse.Spec.GC.Base.heap_size_aligned () Term)
(declare-fun Pulse.Spec.GC.Base.hp_addr () Term)
(declare-fun Pulse.Spec.GC.Base.mword (Dummy_sort) Term)
(declare-fun Pulse.Spec.GC.Fields.field_address (Term Term) Term)
(declare-fun Pulse.Spec.GC.Fields.field_offset (Term) Term)
(declare-fun Pulse.Spec.GC.Fields.hd_address (Term) Term)
(declare-fun Pulse.Spec.GC.Fields.is_pointer (Term) Term)
(declare-fun Pulse.Spec.GC.Fields.is_pointer_field (Term) Term)
(declare-fun Pulse.Spec.GC.Fields.well_formed_object (Term Term) Term)
(declare-fun Pulse.Spec.GC.Fields.wosize () Term)
(declare-fun Pulse.Spec.GC.Graph.edge () Term)
(declare-fun Pulse.Spec.GC.Graph.edge_list () Term)
(declare-fun Pulse.Spec.GC.Graph.vertex_id () Term)
(declare-fun Pulse.Spec.GC.Heap.read_word (Term Term) Term)
(declare-fun Pulse.Spec.GC.Object.wosize_of_object (Term Term) Term)
(declare-fun Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae (Universe Term Term) Term)
(declare-fun Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 (Universe Term) Term)
(declare-fun Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 (Term Term) Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)
(declare-fun Tm_refine_4359097d3114cde82e42170cff13171a () Term)
(declare-fun Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 (Term) Term)
(declare-fun Tm_refine_4db8ba22c4504a66577a2159dcc603cd (Term Term) Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
(declare-fun Tm_refine_543bc9b1f8916528b7c12f0b558d7549 (Term Term) Term)
(declare-fun Tm_refine_6126b634cd1de8db5b181615ce1e7167 () Term)
(declare-fun Tm_refine_774ba3f728d91ead8ef40be66c9802e5 () Term)
(declare-fun Tm_refine_92433d9274bcae522779ce3fab30308e () Term)
(declare-fun Tm_refine_9d6af3f3535473623f7aec2f0501897f () Term)
(declare-fun Tm_refine_9e6c2b710f8774dfb253c8099c62ae93 () Term)
(declare-fun Tm_refine_ba4be9e593fda710cd7cd90723afa87e () Term)
(declare-fun Tm_refine_bc552b2c624e2add758b3ac761c0c563 (Term Term) Term)
(declare-fun Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 (Universe Term Term) Term)
(declare-fun Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb () Term)
(declare-fun Tm_refine_f13070840248fced9d9d60d77bdae3ec (Term) Term)
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple2 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 132)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple2
    (FStar.Pervasives.Native.Mktuple2_@0 __@x0)
    (FStar.Pervasives.Native.Mktuple2_@1 __@x0)
    (FStar.Pervasives.Native.Mktuple2_@_a __@x0)
    (FStar.Pervasives.Native.Mktuple2_@_b __@x0)
    (FStar.Pervasives.Native.Mktuple2_@_1 __@x0)
    (FStar.Pervasives.Native.Mktuple2_@_2 __@x0)))))
; Discriminator definition
(define-fun is-Prims.T ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 122) (= __@x0 Prims.T)))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@x0 Term))
   (! (= (Prims.pow2 @x0) (Prims.pow2.fuel_instrumented MaxFuel @x0))
    :pattern ((Prims.pow2 @x0))
    :qid @fuel_correspondence_Prims.pow2.fuel_instrumented))
  :named @fuel_correspondence_Prims.pow2.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (= (Prims.pow2.fuel_instrumented (SFuel @u0) @x1) (Prims.pow2.fuel_instrumented ZFuel @x1))
    :pattern ((Prims.pow2.fuel_instrumented (SFuel @u0) @x1))
    :qid @fuel_irrelevance_Prims.pow2.fuel_instrumented))
  :named @fuel_irrelevance_Prims.pow2.fuel_instrumented))
; pretyping
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@u3 Universe) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (FStar.Pervasives.Native.tuple2 @u2 @u3 @x4 @x5))
     (= (FStar.Pervasives.Native.tuple2 @u2 @u3 @x4 @x5) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.Pervasives.Native.tuple2 @u2 @u3 @x4 @x5)))
    :qid FStar.Pervasives.Native_pretyping_a0b5b30d6fb83cfcb1f59d80b87f731e))
  :named FStar.Pervasives.Native_pretyping_a0b5b30d6fb83cfcb1f59d80b87f731e))
; pretyping
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (FStar.Seq.Base.seq @u2 @x3))
     (= (FStar.Seq.Base.seq @u2 @x3) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.Seq.Base.seq @u2 @x3)))
    :qid FStar.Seq.Base_pretyping_aec2ec0359b5151fd30ba679a2daadcd))
  :named FStar.Seq.Base_pretyping_aec2ec0359b5151fd30ba679a2daadcd))
; pretyping
;;; Fact-ids: Name FStar.UInt64.t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(48,8-48,9); use=FStar.UInt64.fsti(48,8-48,9)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Dummy_sort))
   (! (implies (HasTypeFuel @u1 @x0 (FStar.UInt64.t @u2)) (= (FStar.UInt64.t @u2) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.UInt64.t @u2)))
    :qid FStar.UInt64_pretyping_0a6d0526dc068d94bc7967094b2dd513))
  :named FStar.UInt64_pretyping_0a6d0526dc068d94bc7967094b2dd513))
; pretyping
;;; Fact-ids: Name FStar.UInt8.t; Namespace FStar.UInt8
(assert
 (! ;; def=FStar.UInt8.fsti(48,8-48,9); use=FStar.UInt8.fsti(48,8-48,9)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Dummy_sort))
   (! (implies (HasTypeFuel @u1 @x0 (FStar.UInt8.t @u2)) (= (FStar.UInt8.t @u2) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (FStar.UInt8.t @u2)))
    :qid FStar.UInt8_pretyping_512f0e4172b97206a8b0e16196475713))
  :named FStar.UInt8_pretyping_512f0e4172b97206a8b0e16196475713))
; interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3))
     (and
      ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
      (forall ((@x4 Term))
       (! (implies
         (HasType @x4 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u1 @x2 @x3))
         (HasType (ApplyTT @x0 @x4) (Tm_type U_zero)))
        :pattern ((ApplyTT @x0 @x4))
        :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u1 @x2 @x3)))
    :qid Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_interpretation_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pre-typing for functions
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u2 @x3 @x4)))
    :qid Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named Prims_pre_typing_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; pretyping
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! ;; def=Prims.fst(522,5-522,8); use=Prims.fst(522,5-522,8)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.int) (= Prims.int (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.int))
    :qid Prims_pretyping_ae567c2fb75be05905677af440075565))
  :named Prims_pretyping_ae567c2fb75be05905677af440075565))
; pretyping
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.trivial) (= Prims.trivial (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.trivial))
    :qid Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
  :named Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
; pretyping
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! ;; def=Prims.fst(88,5-88,9); use=Prims.fst(88,5-88,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.bool) (= Prims.bool (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.bool))
    :qid Prims_pretyping_f537159ed795b314b4e58c260361ae86))
  :named Prims_pretyping_f537159ed795b314b4e58c260361ae86))
; pretyping
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! ;; def=Prims.fst(104,5-104,9); use=Prims.fst(104,5-104,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.unit) (= Prims.unit (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.unit))
    :qid Prims_pretyping_f8666440faa91836cc5a13998af863fc))
  :named Prims_pretyping_f8666440faa91836cc5a13998af863fc))
; Assumption: FStar.Pervasives.Native.tuple2__uu___haseq
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2__uu___haseq; Namespace FStar.Pervasives.Native
(assert
 (! (forall ((@u0 Universe) (@u1 Universe))
   (! (forall ((@x2 Term) (@x3 Term))
     (! (implies
       (and
        (HasType @x2 (Tm_type @u0))
        (HasType @x3 (Tm_type @u1))
        (Valid (Prims.hasEq @u0 @x2))
        (Valid (Prims.hasEq @u1 @x3)))
       (Valid (Prims.hasEq (U_max @u0 @u1) (FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3))))
      :pattern ((Prims.hasEq (U_max @u0 @u1) (FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3)))
      :qid assumption_FStar.Pervasives.Native.tuple2__uu___haseq.1))
    :qid assumption_FStar.Pervasives.Native.tuple2__uu___haseq))
  :named assumption_FStar.Pervasives.Native.tuple2__uu___haseq))
; b2t def
;;; Fact-ids: Name Prims.b2t; Namespace Prims
(assert
 (! ;; def=Prims.fst(188,5-188,8); use=Prims.fst(188,5-188,8)
  (forall ((@x0 Term))
   (! (= (Valid (Prims.b2t @x0)) (BoxBool_proj_0 @x0)) :pattern ((Prims.b2t @x0)) :qid b2t_def))
  :named b2t_def))
; b2t typing
;;; Fact-ids: Name Prims.b2t; Namespace Prims
(assert
 (! ;; def=Prims.fst(188,5-188,8); use=Prims.fst(188,5-188,8)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.bool) (HasType (Prims.b2t @x0) (Tm_type U_zero)))
    :pattern ((Prims.b2t @x0))
    :qid b2t_typing))
  :named b2t_typing))
; bool inversion
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.bool) (is-BoxBool @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.bool))
    :qid bool_inversion))
  :named bool_inversion))
; bool typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Bool))
   (! (HasType (BoxBool @u0) Prims.bool) :pattern ((BoxBool @u0)) :qid bool_typing))
  :named bool_typing))
; Constructor distinct
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= 132 (Term_constr_id (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5)))
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid constructor_distinct_FStar.Pervasives.Native.Mktuple2))
  :named constructor_distinct_FStar.Pervasives.Native.Mktuple2))
; Constructor distinct
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= 125 (Term_constr_id (FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3)))
    :pattern ((FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3))
    :qid constructor_distinct_FStar.Pervasives.Native.tuple2))
  :named constructor_distinct_FStar.Pervasives.Native.tuple2))
; Constructor distinct
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 103 (Term_constr_id (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.seq @u0 @x1))
    :qid constructor_distinct_FStar.Seq.Base.seq))
  :named constructor_distinct_FStar.Seq.Base.seq))
; Constructor distinct
;;; Fact-ids: Name FStar.UInt64.t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(48,8-48,9); use=FStar.UInt64.fsti(48,8-48,9)
  (forall ((@u0 Dummy_sort))
   (! (= 101 (Term_constr_id (FStar.UInt64.t @u0)))
    :pattern ((FStar.UInt64.t @u0))
    :qid constructor_distinct_FStar.UInt64.t))
  :named constructor_distinct_FStar.UInt64.t))
; Constructor distinct
;;; Fact-ids: Name FStar.UInt8.t; Namespace FStar.UInt8
(assert
 (! ;; def=FStar.UInt8.fsti(48,8-48,9); use=FStar.UInt8.fsti(48,8-48,9)
  (forall ((@u0 Dummy_sort))
   (! (= 101 (Term_constr_id (FStar.UInt8.t @u0)))
    :pattern ((FStar.UInt8.t @u0))
    :qid constructor_distinct_FStar.UInt8.t))
  :named constructor_distinct_FStar.UInt8.t))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 122 (Term_constr_id Prims.T)) :named constructor_distinct_Prims.T))
; Constructor distinct
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (= 107 (Term_constr_id Prims.bool)) :named constructor_distinct_Prims.bool))
; Constructor distinct
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (= 303 (Term_constr_id Prims.int)) :named constructor_distinct_Prims.int))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 116 (Term_constr_id Prims.trivial)) :named constructor_distinct_Prims.trivial))
; Constructor distinct
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (= 125 (Term_constr_id Prims.unit)) :named constructor_distinct_Prims.unit))
; data constructor typing elim
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall
    ((@u0 Fuel)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (implies
     (HasTypeFuel
      (SFuel @u0)
      (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
      (FStar.Pervasives.Native.tuple2 @u1 @u2 @x7 @x8))
     (and
      (HasTypeFuel @u0 @x7 (Tm_type @u1))
      (HasTypeFuel @u0 @x8 (Tm_type @u2))
      (HasTypeFuel @u0 @x5 @x7)
      (HasTypeFuel @u0 @x6 @x8)))
    :pattern
     ((HasTypeFuel
       (SFuel @u0)
       (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
       (FStar.Pervasives.Native.tuple2 @u1 @u2 @x7 @x8)))
    :qid data_elim_FStar.Pervasives.Native.Mktuple2))
  :named data_elim_FStar.Pervasives.Native.Mktuple2))
; data constructor typing intro
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Fuel) (@u1 Universe) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x3 (Tm_type @u1))
      (HasTypeFuel @u0 @x4 (Tm_type @u2))
      (HasTypeFuel @u0 @x5 @x3)
      (HasTypeFuel @u0 @x6 @x4))
     (HasTypeFuel
      @u0
      (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
      (FStar.Pervasives.Native.tuple2 @u1 @u2 @x3 @x4)))
    :pattern
     ((HasTypeFuel
       @u0
       (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
       (FStar.Pervasives.Native.tuple2 @u1 @u2 @x3 @x4)))
    :qid data_typing_intro_FStar.Pervasives.Native.Mktuple2@tok))
  :named data_typing_intro_FStar.Pervasives.Native.Mktuple2@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,17-99,18); use=Prims.fst(99,17-99,18)
  (forall ((@u0 Fuel))
   (! (HasTypeFuel @u0 Prims.T Prims.trivial)
    :pattern ((HasTypeFuel @u0 Prims.T Prims.trivial))
    :qid data_typing_intro_Prims.T@tok))
  :named data_typing_intro_Prims.T@tok))
; Prop-typing for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (Valid (Prims.subtype_of U_zero U_zero (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.unit)))
    :pattern ((Prims.subtype_of U_zero U_zero (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.unit))
    :qid defn_equation_Prims.subtype_of))
  :named defn_equation_Prims.subtype_of))
; equality for proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= Prims.T@tok Prims.T) :named equality_tok_Prims.T@tok))
; Equation for FStar.Seq.Base.cons
;;; Fact-ids: Name FStar.Seq.Base.cons; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(60,4-60,8); use=FStar.Seq.Base.fsti(60,4-60,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.Seq.Base.cons @u0 @x1 @x2 @x3)
     (FStar.Seq.Base.append @u0 @x1 (FStar.Seq.Base.create @u0 @x1 (BoxInt 1) @x2) @x3))
    :pattern ((FStar.Seq.Base.cons @u0 @x1 @x2 @x3))
    :qid equation_FStar.Seq.Base.cons))
  :named equation_FStar.Seq.Base.cons))
; Equation for FStar.UInt.fits
;;; Fact-ids: Name FStar.UInt.fits; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(49,4-49,8); use=FStar.UInt.fsti(49,4-49,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (FStar.UInt.fits @x0 @x1)
     (Prims.op_AmpAmp
      (Prims.op_LessThanOrEqual (FStar.UInt.min_int @x1) @x0)
      (Prims.op_LessThanOrEqual @x0 (FStar.UInt.max_int @x1))))
    :pattern ((FStar.UInt.fits @x0 @x1))
    :qid equation_FStar.UInt.fits))
  :named equation_FStar.UInt.fits))
; Equation for FStar.UInt.max_int
;;; Fact-ids: Name FStar.UInt.max_int; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(46,4-46,11); use=FStar.UInt.fsti(46,4-46,11)
  (forall ((@x0 Term))
   (! (= (FStar.UInt.max_int @x0) (Prims.op_Subtraction (Prims.pow2 @x0) (BoxInt 1)))
    :pattern ((FStar.UInt.max_int @x0))
    :qid equation_FStar.UInt.max_int))
  :named equation_FStar.UInt.max_int))
; Equation for FStar.UInt.min_int
;;; Fact-ids: Name FStar.UInt.min_int; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(47,4-47,11); use=FStar.UInt.fsti(47,4-47,11)
  (forall ((@x0 Term))
   (! (= (FStar.UInt.min_int @x0) (BoxInt 0))
    :pattern ((FStar.UInt.min_int @x0))
    :qid equation_FStar.UInt.min_int))
  :named equation_FStar.UInt.min_int))
; Equation for FStar.UInt.size
;;; Fact-ids: Name FStar.UInt.size; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(50,4-50,8); use=FStar.UInt.fsti(50,4-50,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (FStar.UInt.size @x0 @x1) (Prims.b2t (FStar.UInt.fits @x0 @x1)))
    :pattern ((FStar.UInt.size @x0 @x1))
    :qid equation_FStar.UInt.size))
  :named equation_FStar.UInt.size))
; Equation for FStar.UInt.uint_t
;;; Fact-ids: Name FStar.UInt.uint_t; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(54,5-54,11); use=FStar.UInt.fsti(54,5-54,11)
  (forall ((@x0 Term))
   (! (= (FStar.UInt.uint_t @x0) (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x0))
    :pattern ((FStar.UInt.uint_t @x0))
    :qid equation_FStar.UInt.uint_t))
  :named equation_FStar.UInt.uint_t))
; Equation for Prims.eqtype
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (= Prims.eqtype Tm_refine_9d6af3f3535473623f7aec2f0501897f) :named equation_Prims.eqtype))
; Equation for Prims.l_True
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (= Prims.l_True (Prims.squash U_zero Prims.trivial)) :named equation_Prims.l_True))
; Equation for Prims.logical
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (= Prims.logical (Tm_type U_zero)) :named equation_Prims.logical))
; Equation for Prims.nat
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (= Prims.nat Tm_refine_542f9d4f129664613f2483a6c88bc7c2) :named equation_Prims.nat))
; Equation for Prims.pos
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (= Prims.pos Tm_refine_774ba3f728d91ead8ef40be66c9802e5) :named equation_Prims.pos))
; Equation for Prims.prop
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (= Prims.prop Tm_refine_ba4be9e593fda710cd7cd90723afa87e) :named equation_Prims.prop))
; Equation for Prims.pure_post
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.pure_post @u0 @x1) (Prims.pure_post_ @u0 U_zero @x1 Prims.l_True))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid equation_Prims.pure_post))
  :named equation_Prims.pure_post))
; Equation for Prims.pure_post'
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (= (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x3 @x2))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid equation_Prims.pure_post_))
  :named equation_Prims.pure_post_))
; Equation for Prims.squash
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.squash @u0 @x1) (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x1))
    :pattern ((Prims.squash @u0 @x1))
    :qid equation_Prims.squash))
  :named equation_Prims.squash))
; Equation for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (=
     (Valid (Prims.subtype_of @u0 @u1 @x2 @x3))
     ;; def=Prims.fst(299,31-299,60); use=Prims.fst(299,31-299,60)
     (forall ((@x4 Term))
      (! (implies (HasType @x4 @x2) (HasType @x4 @x3)) :qid equation_Prims.subtype_of.1)))
    :pattern ((Prims.subtype_of @u0 @u1 @x2 @x3))
    :qid equation_Prims.subtype_of))
  :named equation_Prims.subtype_of))
; Equation for Pulse.Spec.GC.Base.heap
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! (= Pulse.Spec.GC.Base.heap Tm_refine_92433d9274bcae522779ce3fab30308e)
  :named equation_Pulse.Spec.GC.Base.heap))
; Equation for Pulse.Spec.GC.Base.heap_size
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(26,4-26,13); use=Pulse.Spec.GC.Base.fsti(26,4-26,13)
  (forall ((@u0 Dummy_sort))
   (! (=
     ;; def=Pulse.Spec.GC.Base.fsti(26,4-26,13); use=Pulse.Spec.GC.Base.fsti(26,4-26,13)
     (Pulse.Spec.GC.Base.heap_size @u0)
     (BoxInt 1024))
    :pattern
     (;; def=Pulse.Spec.GC.Base.fsti(26,4-26,13); use=Pulse.Spec.GC.Base.fsti(26,4-26,13)
      (Pulse.Spec.GC.Base.heap_size @u0))
    :qid equation_Pulse.Spec.GC.Base.heap_size))
  :named equation_Pulse.Spec.GC.Base.heap_size))
; Equation for Pulse.Spec.GC.Base.hp_addr
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! (= Pulse.Spec.GC.Base.hp_addr Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb)
  :named equation_Pulse.Spec.GC.Base.hp_addr))
; Equation for Pulse.Spec.GC.Base.mword
;;; Fact-ids: Name Pulse.Spec.GC.Base.mword; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(23,4-23,9); use=Pulse.Spec.GC.Base.fsti(23,4-23,9)
  (forall ((@u0 Dummy_sort))
   (! (=
     ;; def=Pulse.Spec.GC.Base.fsti(23,4-23,9); use=Pulse.Spec.GC.Base.fsti(23,4-23,9)
     (Pulse.Spec.GC.Base.mword @u0)
     (FStar.UInt64.uint_to_t (BoxInt 8)))
    :pattern
     (;; def=Pulse.Spec.GC.Base.fsti(23,4-23,9); use=Pulse.Spec.GC.Base.fsti(23,4-23,9)
      (Pulse.Spec.GC.Base.mword @u0))
    :qid equation_Pulse.Spec.GC.Base.mword))
  :named equation_Pulse.Spec.GC.Base.mword))
; Equation for Pulse.Spec.GC.Fields.field_address
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(58,4-58,17); use=Pulse.Spec.GC.Fields.fst(58,4-58,17)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Pulse.Spec.GC.Fields.field_address @x0 @x1)
     (FStar.UInt64.add @x0 (Pulse.Spec.GC.Fields.field_offset @x1)))
    :pattern ((Pulse.Spec.GC.Fields.field_address @x0 @x1))
    :qid equation_Pulse.Spec.GC.Fields.field_address))
  :named equation_Pulse.Spec.GC.Fields.field_address))
; Equation for Pulse.Spec.GC.Fields.field_offset
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_offset; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(47,4-47,16); use=Pulse.Spec.GC.Fields.fst(47,4-47,16)
  (forall ((@x0 Term))
   (! (=
     (Pulse.Spec.GC.Fields.field_offset @x0)
     (FStar.UInt64.mul @x0 (Pulse.Spec.GC.Base.mword Dummy_value)))
    :pattern ((Pulse.Spec.GC.Fields.field_offset @x0))
    :qid equation_Pulse.Spec.GC.Fields.field_offset))
  :named equation_Pulse.Spec.GC.Fields.field_offset))
; Equation for Pulse.Spec.GC.Fields.hd_address
;;; Fact-ids: Name Pulse.Spec.GC.Fields.hd_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(32,4-32,14); use=Pulse.Spec.GC.Fields.fst(32,4-32,14)
  (forall ((@x0 Term))
   (! (=
     (Pulse.Spec.GC.Fields.hd_address @x0)
     (let ((@lb1 (Prims.op_GreaterThanOrEqual (FStar.UInt64.v @x0) (BoxInt 8))))
      (ite
       (= @lb1 (BoxBool true))
       (FStar.UInt64.sub @x0 (Pulse.Spec.GC.Base.mword Dummy_value))
       (FStar.UInt64.uint_to_t (BoxInt 0)))))
    :pattern ((Pulse.Spec.GC.Fields.hd_address @x0))
    :qid equation_Pulse.Spec.GC.Fields.hd_address))
  :named equation_Pulse.Spec.GC.Fields.hd_address))
; Equation for Pulse.Spec.GC.Fields.is_pointer
;;; Fact-ids: Name Pulse.Spec.GC.Fields.is_pointer; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(71,4-71,14); use=Pulse.Spec.GC.Fields.fst(71,4-71,14)
  (forall ((@x0 Term))
   (! (=
     (Pulse.Spec.GC.Fields.is_pointer @x0)
     (Prims.op_AmpAmp
      (Prims.op_AmpAmp
       (Prims.op_GreaterThanOrEqual (FStar.UInt64.v @x0) (BoxInt 8))
       (Prims.op_LessThan (FStar.UInt64.v @x0) (Pulse.Spec.GC.Base.heap_size Dummy_value)))
      (Prims.op_Equality Prims.int (Prims.op_Modulus (FStar.UInt64.v @x0) (BoxInt 8)) (BoxInt 0))))
    :pattern ((Pulse.Spec.GC.Fields.is_pointer @x0))
    :qid equation_Pulse.Spec.GC.Fields.is_pointer))
  :named equation_Pulse.Spec.GC.Fields.is_pointer))
; Equation for Pulse.Spec.GC.Fields.is_pointer_field
;;; Fact-ids: Name Pulse.Spec.GC.Fields.is_pointer_field; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(75,4-75,20); use=Pulse.Spec.GC.Fields.fst(75,4-75,20)
  (forall ((@x0 Term))
   (! (= (Pulse.Spec.GC.Fields.is_pointer_field @x0) (Pulse.Spec.GC.Fields.is_pointer @x0))
    :pattern ((Pulse.Spec.GC.Fields.is_pointer_field @x0))
    :qid equation_Pulse.Spec.GC.Fields.is_pointer_field))
  :named equation_Pulse.Spec.GC.Fields.is_pointer_field))
; Equation for Pulse.Spec.GC.Fields.well_formed_object
;;; Fact-ids: Name Pulse.Spec.GC.Fields.well_formed_object; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(83,4-83,22); use=Pulse.Spec.GC.Fields.fst(83,4-83,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Pulse.Spec.GC.Fields.well_formed_object @x0 @x1)
     (Prims.b2t
      (Prims.op_LessThanOrEqual
       (Prims.op_Addition
        (Prims.op_Addition (FStar.UInt64.v (Pulse.Spec.GC.Fields.hd_address @x1)) (BoxInt 8))
        (Prims.op_Multiply
         (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x1 @x0))
         (BoxInt 8)))
       (Pulse.Spec.GC.Base.heap_size Dummy_value))))
    :pattern ((Pulse.Spec.GC.Fields.well_formed_object @x0 @x1))
    :qid equation_Pulse.Spec.GC.Fields.well_formed_object))
  :named equation_Pulse.Spec.GC.Fields.well_formed_object))
; Equation for Pulse.Spec.GC.Fields.wosize
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! (= Pulse.Spec.GC.Fields.wosize Tm_refine_9e6c2b710f8774dfb253c8099c62ae93)
  :named equation_Pulse.Spec.GC.Fields.wosize))
; Equation for Pulse.Spec.GC.Graph.edge
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge; Namespace Pulse.Spec.GC.Graph
(assert
 (! (=
   Pulse.Spec.GC.Graph.edge
   (FStar.Pervasives.Native.tuple2
    U_zero
    U_zero
    Pulse.Spec.GC.Graph.vertex_id
    Pulse.Spec.GC.Graph.vertex_id))
  :named equation_Pulse.Spec.GC.Graph.edge))
; Equation for Pulse.Spec.GC.Graph.edge_list
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (= Pulse.Spec.GC.Graph.edge_list (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.edge))
  :named equation_Pulse.Spec.GC.Graph.edge_list))
; Equation for Pulse.Spec.GC.Graph.vertex_id
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_id; Namespace Pulse.Spec.GC.Graph
(assert
 (! (= Pulse.Spec.GC.Graph.vertex_id Pulse.Spec.GC.Base.hp_addr)
  :named equation_Pulse.Spec.GC.Graph.vertex_id))
; Equation for fuel-instrumented recursive function: Prims.pow2
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasType @x1 Prims.nat)
     (=
      (Prims.pow2.fuel_instrumented (SFuel @u0) @x1)
      (let ((@lb2 @x1))
       (ite
        (= @lb2 (BoxInt 0))
        (BoxInt 1)
        (Prims.op_Multiply
         (BoxInt 2)
         (Prims.pow2.fuel_instrumented @u0 (Prims.op_Subtraction @x1 (BoxInt 1))))))))
    :weight 0
    :pattern ((Prims.pow2.fuel_instrumented (SFuel @u0) @x1))
    :qid equation_with_fuel_Prims.pow2.fuel_instrumented))
  :named equation_with_fuel_Prims.pow2.fuel_instrumented))
; fresh token
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! (forall ((@u0 Universe) (@u1 Universe))
   (! (= 126 (Term_constr_id (FStar.Pervasives.Native.tuple2@tok @u0 @u1)))
    :pattern ((FStar.Pervasives.Native.tuple2@tok @u0 @u1))
    :qid fresh_token_FStar.Pervasives.Native.tuple2@tok))
  :named fresh_token_FStar.Pervasives.Native.tuple2@tok))
; inversion axiom
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@u3 Universe) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (FStar.Pervasives.Native.tuple2 @u2 @u3 @x4 @x5))
     (and
      (is-FStar.Pervasives.Native.Mktuple2 @x1)
      (= @u2 (FStar.Pervasives.Native.Mktuple2_@0 @x1))
      (= @u3 (FStar.Pervasives.Native.Mktuple2_@1 @x1))
      (= @x4 (FStar.Pervasives.Native.Mktuple2_@_a @x1))
      (= @x5 (FStar.Pervasives.Native.Mktuple2_@_b @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (FStar.Pervasives.Native.tuple2 @u2 @u3 @x4 @x5)))
    :qid fuel_guarded_inversion_FStar.Pervasives.Native.tuple2))
  :named fuel_guarded_inversion_FStar.Pervasives.Native.tuple2))
; inversion axiom
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.trivial) (is-Prims.T @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.trivial))
    :qid fuel_guarded_inversion_Prims.trivial))
  :named fuel_guarded_inversion_Prims.trivial))
; function token typing
;;; Fact-ids: Name Prims.__cache_version_number__; Namespace Prims
(assert
 (! (HasType Prims.__cache_version_number__ Prims.int)
  :named function_token_typing_Prims.__cache_version_number__))
; function token typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named function_token_typing_Prims.bool))
; function token typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.eqtype))
; function token typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named function_token_typing_Prims.int))
; function token typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named function_token_typing_Prims.l_True))
; function token typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.logical))
; function token typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named function_token_typing_Prims.nat))
; function token typing
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Prims.pos (Tm_type U_zero)) :named function_token_typing_Prims.pos))
; function token typing
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Prims.prop (Tm_type (U_succ U_zero))) :named function_token_typing_Prims.prop))
; function token typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named function_token_typing_Prims.unit))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.heap (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Base.heap))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size_aligned; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.heap_size_aligned Tm_refine_4359097d3114cde82e42170cff13171a)
  :named function_token_typing_Pulse.Spec.GC.Base.heap_size_aligned))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.hp_addr (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Base.hp_addr))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! (HasType Pulse.Spec.GC.Fields.wosize (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Fields.wosize))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.edge (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Graph.edge))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.edge_list (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Graph.edge_list))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_id; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.vertex_id (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Graph.vertex_id))
; haseq for Tm_refine_0ce91af3d6762ea7d913b870f9e33a01
;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,26-46,49); use=FStar.Seq.Base.fsti(46,26-46,49)
  (forall ((@u0 Universe) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u0 @x1)))
     (Valid (Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1))))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u0 @x1))))
    :qid haseqTm_refine_0ce91af3d6762ea7d913b870f9e33a01))
  :named haseqTm_refine_0ce91af3d6762ea7d913b870f9e33a01))
; haseq for Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136
;;; Fact-ids: Name FStar.UInt64.mul; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(144,27-144,28); use=FStar.UInt64.fsti(144,27-144,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x0 @x1)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x0 @x1))))
    :qid haseqTm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
  :named haseqTm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
; haseq for Tm_refine_2de20c066034c13bf76e9c0b94f4806c
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0))))
    :qid haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
; haseq for Tm_refine_4359097d3114cde82e42170cff13171a
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size_aligned; Namespace Pulse.Spec.GC.Base
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_4359097d3114cde82e42170cff13171a))
   (Valid (Prims.hasEq U_zero Prims.unit)))
  :named haseqTm_refine_4359097d3114cde82e42170cff13171a))
; haseq for Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4
;;; Fact-ids: Name FStar.UInt64.uint_to_t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(58,34-58,35); use=FStar.UInt64.fsti(58,34-58,35)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x0)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x0))))
    :qid haseqTm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
  :named haseqTm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
; haseq for Tm_refine_4db8ba22c4504a66577a2159dcc603cd
;;; Fact-ids: Name FStar.UInt64.sub; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(116,27-116,28); use=FStar.UInt64.fsti(116,27-116,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x0 @x1)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x0 @x1))))
    :qid haseqTm_refine_4db8ba22c4504a66577a2159dcc603cd))
  :named haseqTm_refine_4db8ba22c4504a66577a2159dcc603cd))
; haseq for Tm_refine_542f9d4f129664613f2483a6c88bc7c2
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_542f9d4f129664613f2483a6c88bc7c2))
; haseq for Tm_refine_543bc9b1f8916528b7c12f0b558d7549
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(59,9-59,16); use=Pulse.Spec.GC.Fields.fst(59,9-59,16)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x0 @x1)))
     (Valid (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x0 @x1))))
    :qid haseqTm_refine_543bc9b1f8916528b7c12f0b558d7549))
  :named haseqTm_refine_543bc9b1f8916528b7c12f0b558d7549))
; haseq for Tm_refine_6126b634cd1de8db5b181615ce1e7167
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_offset; Namespace Pulse.Spec.GC.Fields
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_6126b634cd1de8db5b181615ce1e7167))
   (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
  :named haseqTm_refine_6126b634cd1de8db5b181615ce1e7167))
; haseq for Tm_refine_774ba3f728d91ead8ef40be66c9802e5
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_774ba3f728d91ead8ef40be66c9802e5))
; haseq for Tm_refine_92433d9274bcae522779ce3fab30308e
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_92433d9274bcae522779ce3fab30308e))
   (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero (FStar.UInt8.t Dummy_value)))))
  :named haseqTm_refine_92433d9274bcae522779ce3fab30308e))
; haseq for Tm_refine_9d6af3f3535473623f7aec2f0501897f
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_9d6af3f3535473623f7aec2f0501897f))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_9d6af3f3535473623f7aec2f0501897f))
; haseq for Tm_refine_9e6c2b710f8774dfb253c8099c62ae93
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_9e6c2b710f8774dfb253c8099c62ae93))
   (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
  :named haseqTm_refine_9e6c2b710f8774dfb253c8099c62ae93))
; haseq for Tm_refine_ba4be9e593fda710cd7cd90723afa87e
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq (U_succ U_zero) Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
   (Valid (Prims.hasEq (U_succ U_zero) (Tm_type U_zero))))
  :named haseqTm_refine_ba4be9e593fda710cd7cd90723afa87e))
; haseq for Tm_refine_bc552b2c624e2add758b3ac761c0c563
;;; Fact-ids: Name FStar.UInt64.add; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(88,27-88,28); use=FStar.UInt64.fsti(88,27-88,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x0 @x1)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x0 @x1))))
    :qid haseqTm_refine_bc552b2c624e2add758b3ac761c0c563))
  :named haseqTm_refine_bc552b2c624e2add758b3ac761c0c563))
; haseq for Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2)))
     (Valid (Prims.hasEq @u0 @x2)))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2))))
    :qid haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named haseqTm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; haseq for Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
   (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
  :named haseqTm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
; haseq for Tm_refine_f13070840248fced9d9d60d77bdae3ec
;;; Fact-ids: Name FStar.UInt.uint_t; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(54,22-54,37); use=FStar.UInt.fsti(54,22-54,37)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x0)))
     (Valid (Prims.hasEq U_zero Prims.int)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x0))))
    :qid haseqTm_refine_f13070840248fced9d9d60d77bdae3ec))
  :named haseqTm_refine_f13070840248fced9d9d60d77bdae3ec))
; int inversion
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.int) (is-BoxInt @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.int))
    :qid int_inversion))
  :named int_inversion))
; int typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Int)) (! (HasType (BoxInt @u0) Prims.int) :pattern ((BoxInt @u0)) :qid int_typing))
  :named int_typing))
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! (and
   ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
   (forall ((@u0 Universe) (@u1 Universe))
    (! (IsTotFun (FStar.Pervasives.Native.tuple2@tok @u0 @u1))
     :pattern ((FStar.Pervasives.Native.tuple2@tok @u0 @u1))
     :qid kinding_FStar.Pervasives.Native.tuple2@tok))
   ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
   (forall ((@u0 Universe) (@u1 Universe) (@x2 Term))
    (! (IsTotFun (ApplyTT (FStar.Pervasives.Native.tuple2@tok @u0 @u1) @x2))
     :pattern ((ApplyTT (FStar.Pervasives.Native.tuple2@tok @u0 @u1) @x2))
     :qid kinding_FStar.Pervasives.Native.tuple2@tok.1))
   ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
   (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
    (! (implies
      (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
      (HasType (FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3) (Tm_type (U_max @u0 @u1))))
     :pattern ((FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3))
     :qid kinding_FStar.Pervasives.Native.tuple2@tok.2)))
  :named kinding_FStar.Pervasives.Native.tuple2@tok))
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.trivial (Tm_type U_zero)) :named kinding_Prims.trivial@tok))
; kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType
     (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
     (Tm_type (U_max (U_succ U_zero) @u0)))
    :pattern
     ((HasType
       (Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae @u0 @x1 @x2)
       (Tm_type (U_max (U_succ U_zero) @u0))))
    :qid kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
  :named kinding_Tm_arrow_0c3c8e2d803cb8bc23be0650e50367ae))
; Lemma: FStar.Seq.Base.hasEq_lemma
;;; Fact-ids: Name FStar.Seq.Base.hasEq_lemma; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      ;; def=FStar.Seq.Base.fsti(163,43-163,52); use=FStar.Seq.Base.fsti(163,43-163,52)
      (Valid
       ;; def=FStar.Seq.Base.fsti(163,43-163,52); use=FStar.Seq.Base.fsti(163,43-163,52)
       (Prims.hasEq @u0 @x1)))
     ;; def=FStar.Seq.Base.fsti(163,63-163,78); use=FStar.Seq.Base.fsti(163,63-163,78)
     (Valid
      ;; def=FStar.Seq.Base.fsti(163,63-163,78); use=FStar.Seq.Base.fsti(163,63-163,78)
      (Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1))))
    :pattern ((Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1)))
    :qid lemma_FStar.Seq.Base.hasEq_lemma))
  :named lemma_FStar.Seq.Base.hasEq_lemma))
; Lemma: FStar.Seq.Base.lemma_create_len
;;; Fact-ids: Name FStar.Seq.Base.lemma_create_len; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 Prims.nat) (HasType @x3 @x1))
     ;; def=FStar.Seq.Base.fsti(94,11-94,36); use=FStar.Seq.Base.fsti(94,11-94,36)
     (= (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.create @u0 @x1 @x2 @x3)) @x2))
    :pattern ((FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.create @u0 @x1 @x2 @x3)))
    :qid lemma_FStar.Seq.Base.lemma_create_len))
  :named lemma_FStar.Seq.Base.lemma_create_len))
; Lemma: FStar.Seq.Base.lemma_len_append
;;; Fact-ids: Name FStar.Seq.Base.lemma_len_append; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (FStar.Seq.Base.seq @u0 @x1)))
     ;; def=FStar.Seq.Base.fsti(124,11-124,58); use=FStar.Seq.Base.fsti(124,11-124,58)
     (=
      (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3))
      (Prims.op_Addition (FStar.Seq.Base.length @u0 @x1 @x2) (FStar.Seq.Base.length @u0 @x1 @x3))))
    :pattern ((FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3)))
    :qid lemma_FStar.Seq.Base.lemma_len_append))
  :named lemma_FStar.Seq.Base.lemma_len_append))
; Lemma: FStar.UInt.pow2_values
;;; Fact-ids: Name FStar.UInt.pow2_values; Namespace FStar.UInt
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Prims.nat)
     (let ((@lb1 @x0))
      (ite
       (= @lb1 (BoxInt 0))
       ;; def=FStar.UInt.fsti(28,11-28,14); use=FStar.UInt.fsti(28,11-28,14)
       (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 1))
       (ite
        (= @lb1 (BoxInt 1))
        ;; def=FStar.UInt.fsti(29,11-29,14); use=FStar.UInt.fsti(29,11-29,14)
        (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2))
        (ite
         (= @lb1 (BoxInt 8))
         ;; def=FStar.UInt.fsti(30,11-30,16); use=FStar.UInt.fsti(30,11-30,16)
         (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 256))
         (ite
          (= @lb1 (BoxInt 16))
          ;; def=FStar.UInt.fsti(31,11-31,18); use=FStar.UInt.fsti(31,11-31,18)
          (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 65536))
          (ite
           (= @lb1 (BoxInt 31))
           ;; def=FStar.UInt.fsti(32,11-32,23); use=FStar.UInt.fsti(32,11-32,23)
           (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 2147483648))
           (ite
            (= @lb1 (BoxInt 32))
            ;; def=FStar.UInt.fsti(33,11-33,23); use=FStar.UInt.fsti(33,11-33,23)
            (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 4294967296))
            (ite
             (= @lb1 (BoxInt 63))
             ;; def=FStar.UInt.fsti(34,11-34,32); use=FStar.UInt.fsti(34,11-34,32)
             (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 9223372036854775808))
             (ite
              (= @lb1 (BoxInt 64))
              ;; def=FStar.UInt.fsti(35,11-35,33); use=FStar.UInt.fsti(35,11-35,33)
              (= (Prims.pow2.fuel_instrumented ZFuel @x0) (BoxInt 18446744073709551616))
              (implies
               (= @lb1 (BoxInt 128))
               ;; def=FStar.UInt.fsti(36,12-36,49); use=FStar.UInt.fsti(36,12-36,49)
               (=
                (Prims.pow2.fuel_instrumented ZFuel @x0)
                (BoxInt 340282366920938463463374607431768211456)))))))))))))
    :pattern ((Prims.pow2.fuel_instrumented ZFuel @x0))
    :qid lemma_FStar.UInt.pow2_values))
  :named lemma_FStar.UInt.pow2_values))
; Lemma: FStar.UInt64.uv_inv
;;; Fact-ids: Name FStar.UInt64.uv_inv; Namespace FStar.UInt64
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt64.t Dummy_value))
     ;; def=FStar.UInt64.fsti(64,11-64,33); use=FStar.UInt64.fsti(64,11-64,33)
     (= (FStar.UInt64.uint_to_t (FStar.UInt64.v @x0)) @x0))
    :pattern ((FStar.UInt64.v @x0))
    :qid lemma_FStar.UInt64.uv_inv))
  :named lemma_FStar.UInt64.uv_inv))
; Lemma: FStar.UInt64.vu_inv
;;; Fact-ids: Name FStar.UInt64.vu_inv; Namespace FStar.UInt64
(assert
 (! (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt.uint_t (BoxInt 64)))
     ;; def=FStar.UInt64.fsti(69,11-69,33); use=FStar.UInt64.fsti(69,11-69,33)
     (= (FStar.UInt64.v (FStar.UInt64.uint_to_t @x0)) @x0))
    :pattern ((FStar.UInt64.uint_to_t @x0))
    :qid lemma_FStar.UInt64.vu_inv))
  :named lemma_FStar.UInt64.vu_inv))
; kinding
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
  (forall ((@u0 Universe) (@u1 Universe))
   (! (is-Tm_arrow (PreType (FStar.Pervasives.Native.tuple2@tok @u0 @u1)))
    :pattern ((FStar.Pervasives.Native.tuple2@tok @u0 @u1))
    :qid pre_kinding_FStar.Pervasives.Native.tuple2@tok))
  :named pre_kinding_FStar.Pervasives.Native.tuple2@tok))
;;; Fact-ids: Name Prims.op_Addition; Namespace Prims
(assert
 (! ;; def=Prims.fst(560,4-560,15); use=Prims.fst(560,4-560,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Addition @x0 @x1) (BoxInt (+ (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Addition @x0 @x1))
    :qid primitive_Prims.op_Addition))
  :named primitive_Prims.op_Addition))
;;; Fact-ids: Name Prims.op_AmpAmp; Namespace Prims
(assert
 (! ;; def=Prims.fst(530,4-530,13); use=Prims.fst(530,4-530,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_AmpAmp @x0 @x1) (BoxBool (and (BoxBool_proj_0 @x0) (BoxBool_proj_0 @x1))))
    :pattern ((Prims.op_AmpAmp @x0 @x1))
    :qid primitive_Prims.op_AmpAmp))
  :named primitive_Prims.op_AmpAmp))
;;; Fact-ids: Name Prims.op_Equality; Namespace Prims
(assert
 (! ;; def=Prims.fst(596,4-596,15); use=Prims.fst(596,4-596,15)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (Prims.op_Equality @x0 @x1 @x2) (BoxBool (= @x1 @x2)))
    :pattern ((Prims.op_Equality @x0 @x1 @x2))
    :qid primitive_Prims.op_Equality))
  :named primitive_Prims.op_Equality))
;;; Fact-ids: Name Prims.op_GreaterThanOrEqual; Namespace Prims
(assert
 (! ;; def=Prims.fst(584,4-584,25); use=Prims.fst(584,4-584,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Prims.op_GreaterThanOrEqual @x0 @x1)
     (BoxBool (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_GreaterThanOrEqual))
  :named primitive_Prims.op_GreaterThanOrEqual))
;;; Fact-ids: Name Prims.op_LessThan; Namespace Prims
(assert
 (! ;; def=Prims.fst(590,4-590,15); use=Prims.fst(590,4-590,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThan @x0 @x1) (BoxBool (< (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThan @x0 @x1))
    :qid primitive_Prims.op_LessThan))
  :named primitive_Prims.op_LessThan))
;;; Fact-ids: Name Prims.op_LessThanOrEqual; Namespace Prims
(assert
 (! ;; def=Prims.fst(572,4-572,22); use=Prims.fst(572,4-572,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThanOrEqual @x0 @x1) (BoxBool (<= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_LessThanOrEqual))
  :named primitive_Prims.op_LessThanOrEqual))
;;; Fact-ids: Name Prims.op_Modulus; Namespace Prims
(assert
 (! ;; def=Prims.fst(699,4-699,14); use=Prims.fst(699,4-699,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (not (= (BoxInt_proj_0 @x1) 0))
     (= (Prims.op_Modulus @x0 @x1) (BoxInt (mod (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))))
    :pattern ((Prims.op_Modulus @x0 @x1))
    :qid primitive_Prims.op_Modulus))
  :named primitive_Prims.op_Modulus))
;;; Fact-ids: Name Prims.op_Multiply; Namespace Prims
(assert
 (! ;; def=Prims.fst(548,4-548,15); use=Prims.fst(548,4-548,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Multiply @x0 @x1) (BoxInt (* (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Multiply @x0 @x1))
    :qid primitive_Prims.op_Multiply))
  :named primitive_Prims.op_Multiply))
;;; Fact-ids: Name Prims.op_Subtraction; Namespace Prims
(assert
 (! ;; def=Prims.fst(554,4-554,18); use=Prims.fst(554,4-554,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Subtraction @x0 @x1) (BoxInt (- (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Subtraction @x0 @x1))
    :qid primitive_Prims.op_Subtraction))
  :named primitive_Prims.op_Subtraction))
;;; Fact-ids: Name Prims.op_disEquality; Namespace Prims
(assert
 (! ;; def=Prims.fst(602,4-602,18); use=Prims.fst(602,4-602,18)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (Prims.op_disEquality @x0 @x1 @x2) (BoxBool (not (= @x1 @x2))))
    :pattern ((Prims.op_disEquality @x0 @x1 @x2))
    :qid primitive_Prims.op_disEquality))
  :named primitive_Prims.op_disEquality))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@0 (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @u0)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@0))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@0))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@1 (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @u1)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@1))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@1))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@_1
      (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @x4)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@_1))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@_1))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@_2
      (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @x5)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@_2))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@_2))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@_a
      (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @x2)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@_a))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@_a))
; Projection inverse
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (=
     (FStar.Pervasives.Native.Mktuple2_@_b
      (FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
     @x3)
    :pattern ((FStar.Pervasives.Native.Mktuple2 @u0 @u1 @x2 @x3 @x4 @x5))
    :qid projection_inverse_FStar.Pervasives.Native.Mktuple2_@_b))
  :named projection_inverse_FStar.Pervasives.Native.Mktuple2_@_b))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,26-46,49); use=FStar.Seq.Base.fsti(46,26-46,49)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq @u2 @x3))
      ;; def=FStar.Seq.Base.fsti(46,37-46,47); use=FStar.Seq.Base.fsti(46,37-46,47)
      (= (FStar.Seq.Base.length @u2 @x3 @x1) (BoxInt 0))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u2 @x3)))
    :qid refinement_interpretation_Tm_refine_0ce91af3d6762ea7d913b870f9e33a01))
  :named refinement_interpretation_Tm_refine_0ce91af3d6762ea7d913b870f9e33a01))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt64.mul; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(144,27-144,28); use=FStar.UInt64.fsti(144,27-144,28)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=FStar.UInt64.fsti(146,21-146,36); use=FStar.UInt64.fsti(146,21-146,36)
      (= (Prims.op_Multiply (FStar.UInt64.v @x2) (FStar.UInt64.v @x3)) (FStar.UInt64.v @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
  :named refinement_interpretation_Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
; refinement_interpretation
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
      (Valid
       ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
       @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2)))
    :qid refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size_aligned; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(29,31-29,61); use=Pulse.Spec.GC.Base.fsti(29,31-29,61)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_4359097d3114cde82e42170cff13171a)
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Pulse.Spec.GC.Base.fsti(29,31-29,61); use=Pulse.Spec.GC.Base.fsti(29,31-29,61)
      (=
       (Prims.op_Modulus
        (Pulse.Spec.GC.Base.heap_size Dummy_value)
        (FStar.UInt64.v (Pulse.Spec.GC.Base.mword Dummy_value)))
       (BoxInt 0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_4359097d3114cde82e42170cff13171a))
    :qid refinement_interpretation_Tm_refine_4359097d3114cde82e42170cff13171a))
  :named refinement_interpretation_Tm_refine_4359097d3114cde82e42170cff13171a))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt64.uint_to_t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(58,34-58,35); use=FStar.UInt64.fsti(58,34-58,35)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x2))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=FStar.UInt64.fsti(60,21-60,28); use=FStar.UInt64.fsti(60,21-60,28)
      (= (FStar.UInt64.v @x1) @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x2)))
    :qid refinement_interpretation_Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
  :named refinement_interpretation_Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt64.sub; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(116,27-116,28); use=FStar.UInt64.fsti(116,27-116,28)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=FStar.UInt64.fsti(118,21-118,36); use=FStar.UInt64.fsti(118,21-118,36)
      (= (Prims.op_Subtraction (FStar.UInt64.v @x2) (FStar.UInt64.v @x3)) (FStar.UInt64.v @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_4db8ba22c4504a66577a2159dcc603cd))
  :named refinement_interpretation_Tm_refine_4db8ba22c4504a66577a2159dcc603cd))
; refinement_interpretation
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! ;; def=Prims.fst(682,11-682,25); use=Prims.fst(682,11-682,25)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(682,18-682,24); use=Prims.fst(682,18-682,24)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
    :qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
  :named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(59,9-59,16); use=Pulse.Spec.GC.Fields.fst(59,9-59,16)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Pulse.Spec.GC.Base.hp_addr)
      ;; def=Pulse.Spec.GC.Fields.fst(61,22-61,80); use=Pulse.Spec.GC.Fields.fst(61,22-61,80)
      (=
       (FStar.UInt64.v @x1)
       (Prims.op_Addition (FStar.UInt64.v @x2) (Prims.op_Multiply (FStar.UInt64.v @x3) (BoxInt 8))))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_543bc9b1f8916528b7c12f0b558d7549))
  :named refinement_interpretation_Tm_refine_543bc9b1f8916528b7c12f0b558d7549))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_offset; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(47,17-47,62); use=Pulse.Spec.GC.Fields.fst(47,17-47,62)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_6126b634cd1de8db5b181615ce1e7167)
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.Fields.fst(47,35-47,60); use=Pulse.Spec.GC.Fields.fst(47,35-47,60)
      (< (BoxInt_proj_0 (FStar.UInt64.v @x1)) (BoxInt_proj_0 (Prims.pow2 (BoxInt 61))))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_6126b634cd1de8db5b181615ce1e7167))
    :qid refinement_interpretation_Tm_refine_6126b634cd1de8db5b181615ce1e7167))
  :named refinement_interpretation_Tm_refine_6126b634cd1de8db5b181615ce1e7167))
; refinement_interpretation
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! ;; def=Prims.fst(685,11-685,24); use=Prims.fst(685,11-685,24)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(685,18-685,23); use=Prims.fst(685,18-685,23)
      (> (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
    :qid refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
  :named refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(36,11-36,48); use=Pulse.Spec.GC.Base.fsti(36,11-36,48)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_92433d9274bcae522779ce3fab30308e)
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero (FStar.UInt8.t Dummy_value)))
      ;; def=Pulse.Spec.GC.Base.fsti(36,22-36,47); use=Pulse.Spec.GC.Base.fsti(36,22-36,47)
      (=
       (FStar.Seq.Base.length U_zero (FStar.UInt8.t Dummy_value) @x1)
       (Pulse.Spec.GC.Base.heap_size Dummy_value))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_92433d9274bcae522779ce3fab30308e))
    :qid refinement_interpretation_Tm_refine_92433d9274bcae522779ce3fab30308e))
  :named refinement_interpretation_Tm_refine_92433d9274bcae522779ce3fab30308e))
; refinement_interpretation
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! ;; def=Prims.fst(81,14-81,31); use=Prims.fst(81,14-81,31)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
      (Valid
       ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
       (Prims.hasEq U_zero @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9d6af3f3535473623f7aec2f0501897f))
    :qid refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
  :named refinement_interpretation_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(25,14-25,40); use=Pulse.Spec.GC.Fields.fst(25,14-25,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9e6c2b710f8774dfb253c8099c62ae93)
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.Fields.fst(25,22-25,39); use=Pulse.Spec.GC.Fields.fst(25,22-25,39)
      (< (BoxInt_proj_0 (FStar.UInt64.v @x1)) (BoxInt_proj_0 (Prims.pow2 (BoxInt 54))))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9e6c2b710f8774dfb253c8099c62ae93))
    :qid refinement_interpretation_Tm_refine_9e6c2b710f8774dfb253c8099c62ae93))
  :named refinement_interpretation_Tm_refine_9e6c2b710f8774dfb253c8099c62ae93))
; refinement_interpretation
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! ;; def=Prims.fst(312,12-312,41); use=Prims.fst(312,12-312,41)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_ba4be9e593fda710cd7cd90723afa87e)
     (and
      (HasTypeFuel @u0 @x1 (Tm_type U_zero))
      ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
      (Valid
       ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
       (Prims.subtype_of U_zero U_zero @x1 Prims.unit))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
    :qid refinement_interpretation_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
  :named refinement_interpretation_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt64.add; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(88,27-88,28); use=FStar.UInt64.fsti(88,27-88,28)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=FStar.UInt64.fsti(90,21-90,36); use=FStar.UInt64.fsti(90,21-90,36)
      (= (Prims.op_Addition (FStar.UInt64.v @x2) (FStar.UInt64.v @x3)) (FStar.UInt64.v @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_bc552b2c624e2add758b3ac761c0c563))
  :named refinement_interpretation_Tm_refine_bc552b2c624e2add758b3ac761c0c563))
; refinement_interpretation
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 @x4)
      ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
      (Valid
       ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
       @x3)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_interpretation_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(43,14-47,1); use=Pulse.Spec.GC.Base.fsti(43,14-47,1)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb)
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.Base.fsti(44,2-44,14)
      (>= (BoxInt_proj_0 (FStar.UInt64.v @x1)) (BoxInt_proj_0 (BoxInt 0)))
      ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.Base.fsti(45,2-45,21)
      (<
       (BoxInt_proj_0 (FStar.UInt64.v @x1))
       (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value)))
      ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.Base.fsti(46,2-46,28)
      (=
       (Prims.op_Modulus
        (FStar.UInt64.v @x1)
        (FStar.UInt64.v (Pulse.Spec.GC.Base.mword Dummy_value)))
       (BoxInt 0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
    :qid refinement_interpretation_Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
  :named refinement_interpretation_Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt.uint_t; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(54,22-54,37); use=FStar.UInt.fsti(54,22-54,37)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=FStar.UInt.fsti(54,28-54,36); use=FStar.UInt.fsti(54,28-54,36)
      (Valid
       ;; def=FStar.UInt.fsti(54,28-54,36); use=FStar.UInt.fsti(54,28-54,36)
       (FStar.UInt.size @x1 @x2))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x2)))
    :qid refinement_interpretation_Tm_refine_f13070840248fced9d9d60d77bdae3ec))
  :named refinement_interpretation_Tm_refine_f13070840248fced9d9d60d77bdae3ec))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,26-46,49); use=FStar.Seq.Base.fsti(46,26-46,49)
  (forall ((@u0 Universe) (@x1 Term))
   (! (HasType (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u0 @x1) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u0 @x1) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_0ce91af3d6762ea7d913b870f9e33a01))
  :named refinement_kinding_Tm_refine_0ce91af3d6762ea7d913b870f9e33a01))
; refinement kinding
;;; Fact-ids: Name FStar.UInt64.mul; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(144,27-144,28); use=FStar.UInt64.fsti(144,27-144,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
  :named refinement_kinding_Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136))
; refinement kinding
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size_aligned; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Tm_refine_4359097d3114cde82e42170cff13171a (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_4359097d3114cde82e42170cff13171a))
; refinement kinding
;;; Fact-ids: Name FStar.UInt64.uint_to_t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(58,34-58,35); use=FStar.UInt64.fsti(58,34-58,35)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
  :named refinement_kinding_Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4))
; refinement kinding
;;; Fact-ids: Name FStar.UInt64.sub; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(116,27-116,28); use=FStar.UInt64.fsti(116,27-116,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_4db8ba22c4504a66577a2159dcc603cd))
  :named refinement_kinding_Tm_refine_4db8ba22c4504a66577a2159dcc603cd))
; refinement kinding
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Tm_refine_542f9d4f129664613f2483a6c88bc7c2 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(59,9-59,16); use=Pulse.Spec.GC.Fields.fst(59,9-59,16)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_543bc9b1f8916528b7c12f0b558d7549))
  :named refinement_kinding_Tm_refine_543bc9b1f8916528b7c12f0b558d7549))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_offset; Namespace Pulse.Spec.GC.Fields
(assert
 (! (HasType Tm_refine_6126b634cd1de8db5b181615ce1e7167 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_6126b634cd1de8db5b181615ce1e7167))
; refinement kinding
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Tm_refine_774ba3f728d91ead8ef40be66c9802e5 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Tm_refine_92433d9274bcae522779ce3fab30308e (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_92433d9274bcae522779ce3fab30308e))
; refinement kinding
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Tm_refine_9d6af3f3535473623f7aec2f0501897f (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_9d6af3f3535473623f7aec2f0501897f))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! (HasType Tm_refine_9e6c2b710f8774dfb253c8099c62ae93 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_9e6c2b710f8774dfb253c8099c62ae93))
; refinement kinding
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Tm_refine_ba4be9e593fda710cd7cd90723afa87e (Tm_type (U_succ U_zero)))
  :named refinement_kinding_Tm_refine_ba4be9e593fda710cd7cd90723afa87e))
; refinement kinding
;;; Fact-ids: Name FStar.UInt64.add; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(88,27-88,28); use=FStar.UInt64.fsti(88,27-88,28)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_bc552b2c624e2add758b3ac761c0c563))
  :named refinement_kinding_Tm_refine_bc552b2c624e2add758b3ac761c0c563))
; refinement kinding
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 @u0 @x1 @x2) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
  :named refinement_kinding_Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_def7cf5be4f20c74ebae2eaa0bf05beb))
; refinement kinding
;;; Fact-ids: Name FStar.UInt.uint_t; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(54,22-54,37); use=FStar.UInt.fsti(54,22-54,37)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_f13070840248fced9d9d60d77bdae3ec @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_f13070840248fced9d9d60d77bdae3ec))
  :named refinement_kinding_Tm_refine_f13070840248fced9d9d60d77bdae3ec))
; subterm ordering
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,22-59,30); use=FStar.Pervasives.Native.fst(59,22-59,30)
  (forall
    ((@u0 Fuel)
     (@u1 Universe)
     (@u2 Universe)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (implies
     (HasTypeFuel
      (SFuel @u0)
      (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
      (FStar.Pervasives.Native.tuple2 @u1 @u2 @x7 @x8))
     (and
      (Valid
       (Prims.precedes
        U_zero
        U_zero
        Prims.lex_t
        Prims.lex_t
        @x5
        (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)))
      (Valid
       (Prims.precedes
        U_zero
        U_zero
        Prims.lex_t
        Prims.lex_t
        @x6
        (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)))))
    :pattern
     ((HasTypeFuel
       (SFuel @u0)
       (FStar.Pervasives.Native.Mktuple2 @u1 @u2 @x3 @x4 @x5 @x6)
       (FStar.Pervasives.Native.tuple2 @u1 @u2 @x7 @x8)))
    :qid subterm_ordering_FStar.Pervasives.Native.Mktuple2))
  :named subterm_ordering_FStar.Pervasives.Native.Mktuple2))
; name-token correspondence
;;; Fact-ids: Name FStar.Pervasives.Native.tuple2; Namespace FStar.Pervasives.Native; Name FStar.Pervasives.Native.Mktuple2; Namespace FStar.Pervasives.Native
(assert
 (! ;; def=FStar.Pervasives.Native.fst(59,5-59,11); use=FStar.Pervasives.Native.fst(59,5-59,11)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (=
     (ApplyTT (ApplyTT (FStar.Pervasives.Native.tuple2@tok @u0 @u1) @x2) @x3)
     (FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3))
    :pattern ((ApplyTT (ApplyTT (FStar.Pervasives.Native.tuple2@tok @u0 @u1) @x2) @x3))
    :pattern ((FStar.Pervasives.Native.tuple2 @u0 @u1 @x2 @x3))
    :qid token_correspondence_FStar.Pervasives.Native.tuple2@tok))
  :named token_correspondence_FStar.Pervasives.Native.tuple2@tok))
; Typing correspondence of token to term
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasType @x1 Prims.nat) (HasType (Prims.pow2.fuel_instrumented @u0 @x1) Prims.pos))
    :pattern ((Prims.pow2.fuel_instrumented @u0 @x1))
    :qid token_correspondence_Prims.pow2.fuel_instrumented))
  :named token_correspondence_Prims.pow2.fuel_instrumented))
; True interpretation
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert (! (Valid Prims.l_True) :named true_interp))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.append; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(58,4-58,10); use=FStar.Seq.Base.fsti(58,4-58,10)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (FStar.Seq.Base.seq @u0 @x1)))
     (HasType (FStar.Seq.Base.append @u0 @x1 @x2 @x3) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.append @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Base.append))
  :named typing_FStar.Seq.Base.append))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.cons; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(60,4-60,8); use=FStar.Seq.Base.fsti(60,4-60,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 @x1) (HasType @x3 (FStar.Seq.Base.seq @u0 @x1)))
     (HasType (FStar.Seq.Base.cons @u0 @x1 @x2 @x3) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.cons @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Base.cons))
  :named typing_FStar.Seq.Base.cons))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.create; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(34,4-34,10); use=FStar.Seq.Base.fsti(34,4-34,10)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 Prims.nat) (HasType @x3 @x1))
     (HasType (FStar.Seq.Base.create @u0 @x1 @x2 @x3) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.create @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Base.create))
  :named typing_FStar.Seq.Base.create))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.empty; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,4-46,9); use=FStar.Seq.Base.fsti(46,4-46,9)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (FStar.Seq.Base.empty @u0 @x1) (Tm_refine_0ce91af3d6762ea7d913b870f9e33a01 @u0 @x1)))
    :pattern ((FStar.Seq.Base.empty @u0 @x1))
    :qid typing_FStar.Seq.Base.empty))
  :named typing_FStar.Seq.Base.empty))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.length; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(26,4-26,10); use=FStar.Seq.Base.fsti(26,4-26,10)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)))
     (HasType (FStar.Seq.Base.length @u0 @x1 @x2) Prims.nat))
    :pattern ((FStar.Seq.Base.length @u0 @x1 @x2))
    :qid typing_FStar.Seq.Base.length))
  :named typing_FStar.Seq.Base.length))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.seq; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(23,8-23,11); use=FStar.Seq.Base.fsti(23,8-23,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (FStar.Seq.Base.seq @u0 @x1) (Tm_type @u0)))
    :pattern ((FStar.Seq.Base.seq @u0 @x1))
    :qid typing_FStar.Seq.Base.seq))
  :named typing_FStar.Seq.Base.seq))
; free var typing
;;; Fact-ids: Name FStar.UInt.fits; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(49,4-49,8); use=FStar.UInt.fsti(49,4-49,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.nat))
     (HasType (FStar.UInt.fits @x0 @x1) Prims.bool))
    :pattern ((FStar.UInt.fits @x0 @x1))
    :qid typing_FStar.UInt.fits))
  :named typing_FStar.UInt.fits))
; free var typing
;;; Fact-ids: Name FStar.UInt.max_int; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(46,4-46,11); use=FStar.UInt.fsti(46,4-46,11)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.nat) (HasType (FStar.UInt.max_int @x0) Prims.int))
    :pattern ((FStar.UInt.max_int @x0))
    :qid typing_FStar.UInt.max_int))
  :named typing_FStar.UInt.max_int))
; free var typing
;;; Fact-ids: Name FStar.UInt.min_int; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(47,4-47,11); use=FStar.UInt.fsti(47,4-47,11)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.nat) (HasType (FStar.UInt.min_int @x0) Prims.int))
    :pattern ((FStar.UInt.min_int @x0))
    :qid typing_FStar.UInt.min_int))
  :named typing_FStar.UInt.min_int))
; free var typing
;;; Fact-ids: Name FStar.UInt.size; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(50,4-50,8); use=FStar.UInt.fsti(50,4-50,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.nat))
     (HasType (FStar.UInt.size @x0 @x1) (Tm_type U_zero)))
    :pattern ((FStar.UInt.size @x0 @x1))
    :qid typing_FStar.UInt.size))
  :named typing_FStar.UInt.size))
; free var typing
;;; Fact-ids: Name FStar.UInt.uint_t; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(54,5-54,11); use=FStar.UInt.fsti(54,5-54,11)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.nat) (HasType (FStar.UInt.uint_t @x0) (Tm_type U_zero)))
    :pattern ((FStar.UInt.uint_t @x0))
    :qid typing_FStar.UInt.uint_t))
  :named typing_FStar.UInt.uint_t))
; free var typing
;;; Fact-ids: Name FStar.UInt64.add; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(88,4-88,7); use=FStar.UInt64.fsti(88,4-88,7)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      ;; def=FStar.UInt64.fsti(89,12-89,32); use=FStar.UInt64.fsti(89,12-89,32)
      (Valid
       ;; def=FStar.UInt64.fsti(89,12-89,32); use=FStar.UInt64.fsti(89,12-89,32)
       (FStar.UInt.size (Prims.op_Addition (FStar.UInt64.v @x0) (FStar.UInt64.v @x1)) (BoxInt 64)))
      (HasType @x0 (FStar.UInt64.t Dummy_value))
      (HasType @x1 (FStar.UInt64.t Dummy_value)))
     (HasType (FStar.UInt64.add @x0 @x1) (Tm_refine_bc552b2c624e2add758b3ac761c0c563 @x0 @x1)))
    :pattern ((FStar.UInt64.add @x0 @x1))
    :qid typing_FStar.UInt64.add))
  :named typing_FStar.UInt64.add))
; free var typing
;;; Fact-ids: Name FStar.UInt64.mul; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(144,4-144,7); use=FStar.UInt64.fsti(144,4-144,7)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      ;; def=FStar.UInt64.fsti(145,12-145,32); use=FStar.UInt64.fsti(145,12-145,32)
      (Valid
       ;; def=FStar.UInt64.fsti(145,12-145,32); use=FStar.UInt64.fsti(145,12-145,32)
       (FStar.UInt.size (Prims.op_Multiply (FStar.UInt64.v @x0) (FStar.UInt64.v @x1)) (BoxInt 64)))
      (HasType @x0 (FStar.UInt64.t Dummy_value))
      (HasType @x1 (FStar.UInt64.t Dummy_value)))
     (HasType (FStar.UInt64.mul @x0 @x1) (Tm_refine_2ac8bed7a6398f84bccb91bd4fed7136 @x0 @x1)))
    :pattern ((FStar.UInt64.mul @x0 @x1))
    :qid typing_FStar.UInt64.mul))
  :named typing_FStar.UInt64.mul))
; free var typing
;;; Fact-ids: Name FStar.UInt64.sub; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(116,4-116,7); use=FStar.UInt64.fsti(116,4-116,7)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      ;; def=FStar.UInt64.fsti(117,12-117,32); use=FStar.UInt64.fsti(117,12-117,32)
      (Valid
       ;; def=FStar.UInt64.fsti(117,12-117,32); use=FStar.UInt64.fsti(117,12-117,32)
       (FStar.UInt.size (Prims.op_Subtraction (FStar.UInt64.v @x0) (FStar.UInt64.v @x1)) (BoxInt 64)))
      (HasType @x0 (FStar.UInt64.t Dummy_value))
      (HasType @x1 (FStar.UInt64.t Dummy_value)))
     (HasType (FStar.UInt64.sub @x0 @x1) (Tm_refine_4db8ba22c4504a66577a2159dcc603cd @x0 @x1)))
    :pattern ((FStar.UInt64.sub @x0 @x1))
    :qid typing_FStar.UInt64.sub))
  :named typing_FStar.UInt64.sub))
; free var typing
;;; Fact-ids: Name FStar.UInt64.t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(48,8-48,9); use=FStar.UInt64.fsti(48,8-48,9)
  (forall ((@u0 Dummy_sort))
   (! (HasType (FStar.UInt64.t @u0) Prims.eqtype)
    :pattern ((FStar.UInt64.t @u0))
    :qid typing_FStar.UInt64.t))
  :named typing_FStar.UInt64.t))
; free var typing
;;; Fact-ids: Name FStar.UInt64.uint_to_t; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(58,4-58,13); use=FStar.UInt64.fsti(58,4-58,13)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt.uint_t (BoxInt 64)))
     (HasType (FStar.UInt64.uint_to_t @x0) (Tm_refine_48c1b5b4c02ad49f0760911a9d4b1fb4 @x0)))
    :pattern ((FStar.UInt64.uint_to_t @x0))
    :qid typing_FStar.UInt64.uint_to_t))
  :named typing_FStar.UInt64.uint_to_t))
; free var typing
;;; Fact-ids: Name FStar.UInt64.v; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(52,4-52,5); use=FStar.UInt64.fsti(52,4-52,5)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt64.t Dummy_value))
     (HasType (FStar.UInt64.v @x0) (FStar.UInt.uint_t (BoxInt 64))))
    :pattern ((FStar.UInt64.v @x0))
    :qid typing_FStar.UInt64.v))
  :named typing_FStar.UInt64.v))
; free var typing
;;; Fact-ids: Name FStar.UInt8.t; Namespace FStar.UInt8
(assert
 (! ;; def=FStar.UInt8.fsti(48,8-48,9); use=FStar.UInt8.fsti(48,8-48,9)
  (forall ((@u0 Dummy_sort))
   (! (HasType (FStar.UInt8.t @u0) Prims.eqtype)
    :pattern ((FStar.UInt8.t @u0))
    :qid typing_FStar.UInt8.t))
  :named typing_FStar.UInt8.t))
; free var typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named typing_Prims.bool))
; free var typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype (Tm_type (U_succ U_zero))) :named typing_Prims.eqtype))
; free var typing
;;; Fact-ids: Name Prims.hasEq; Namespace Prims
(assert
 (! ;; def=Prims.fst(77,5-77,10); use=Prims.fst(77,5-77,10)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.hasEq @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.hasEq @u0 @x1))
    :qid typing_Prims.hasEq))
  :named typing_Prims.hasEq))
; free var typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named typing_Prims.int))
; free var typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named typing_Prims.l_True))
; free var typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical (Tm_type (U_succ U_zero))) :named typing_Prims.logical))
; free var typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat (Tm_type U_zero)) :named typing_Prims.nat))
; free var typing
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Prims.pos (Tm_type U_zero)) :named typing_Prims.pos))
; free var typing
;;; Fact-ids: Name Prims.pow2; Namespace Prims
(assert
 (! ;; def=Prims.fst(710,8-710,12); use=Prims.fst(710,8-710,12)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.nat) (HasType (Prims.pow2 @x0) Prims.pos))
    :pattern ((Prims.pow2 @x0))
    :qid typing_Prims.pow2))
  :named typing_Prims.pow2))
; free var typing
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Prims.prop (Tm_type (U_succ U_zero))) :named typing_Prims.prop))
; free var typing
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies
     (HasType @x1 (Tm_type @u0))
     (HasType (Prims.pure_post @u0 @x1) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post @u0 @x1))
    :qid typing_Prims.pure_post))
  :named typing_Prims.pure_post))
; free var typing
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (HasType (Prims.pure_post_ @u0 @u1 @x2 @x3) (Tm_type (U_max (U_succ U_zero) @u0))))
    :pattern ((Prims.pure_post_ @u0 @u1 @x2 @x3))
    :qid typing_Prims.pure_post_))
  :named typing_Prims.pure_post_))
; free var typing
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@u0 Universe) (@x1 Term))
   (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.squash @u0 @x1) (Tm_type U_zero)))
    :pattern ((Prims.squash @u0 @x1))
    :qid typing_Prims.squash))
  :named typing_Prims.squash))
; free var typing
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@u0 Universe) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u0)) (HasType @x3 (Tm_type @u1)))
     (HasType (Prims.subtype_of @u0 @u1 @x2 @x3) Prims.logical))
    :pattern ((Prims.subtype_of @u0 @u1 @x2 @x3))
    :qid typing_Prims.subtype_of))
  :named typing_Prims.subtype_of))
; free var typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named typing_Prims.unit))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.heap (Tm_type U_zero)) :named typing_Pulse.Spec.GC.Base.heap))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(26,4-26,13); use=Pulse.Spec.GC.Base.fsti(26,4-26,13)
  (forall ((@u0 Dummy_sort))
   (! (HasType (Pulse.Spec.GC.Base.heap_size @u0) Prims.pos)
    :pattern ((Pulse.Spec.GC.Base.heap_size @u0))
    :qid typing_Pulse.Spec.GC.Base.heap_size))
  :named typing_Pulse.Spec.GC.Base.heap_size))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.heap_size_aligned; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.heap_size_aligned Tm_refine_4359097d3114cde82e42170cff13171a)
  :named typing_Pulse.Spec.GC.Base.heap_size_aligned))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.hp_addr; Namespace Pulse.Spec.GC.Base
(assert
 (! (HasType Pulse.Spec.GC.Base.hp_addr (Tm_type U_zero)) :named typing_Pulse.Spec.GC.Base.hp_addr))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Base.mword; Namespace Pulse.Spec.GC.Base
(assert
 (! ;; def=Pulse.Spec.GC.Base.fsti(23,4-23,9); use=Pulse.Spec.GC.Base.fsti(23,4-23,9)
  (forall ((@u0 Dummy_sort))
   (! (HasType (Pulse.Spec.GC.Base.mword @u0) (FStar.UInt64.t Dummy_value))
    :pattern ((Pulse.Spec.GC.Base.mword @u0))
    :qid typing_Pulse.Spec.GC.Base.mword))
  :named typing_Pulse.Spec.GC.Base.mword))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(58,4-58,17); use=Pulse.Spec.GC.Fields.fst(58,4-58,17)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      ;; def=Pulse.Spec.GC.Fields.fst(60,14-60,74); use=Pulse.Spec.GC.Fields.fst(60,14-60,74)
      (<
       (BoxInt_proj_0
        (Prims.op_Addition (FStar.UInt64.v @x0) (Prims.op_Multiply (FStar.UInt64.v @x1) (BoxInt 8))))
       (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value)))
      (HasType @x0 Pulse.Spec.GC.Base.hp_addr)
      (HasType @x1 Tm_refine_6126b634cd1de8db5b181615ce1e7167))
     (HasType
      (Pulse.Spec.GC.Fields.field_address @x0 @x1)
      (Tm_refine_543bc9b1f8916528b7c12f0b558d7549 @x0 @x1)))
    :pattern ((Pulse.Spec.GC.Fields.field_address @x0 @x1))
    :qid typing_Pulse.Spec.GC.Fields.field_address))
  :named typing_Pulse.Spec.GC.Fields.field_address))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.field_offset; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(47,4-47,16); use=Pulse.Spec.GC.Fields.fst(47,4-47,16)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Tm_refine_6126b634cd1de8db5b181615ce1e7167)
     (HasType (Pulse.Spec.GC.Fields.field_offset @x0) (FStar.UInt64.t Dummy_value)))
    :pattern ((Pulse.Spec.GC.Fields.field_offset @x0))
    :qid typing_Pulse.Spec.GC.Fields.field_offset))
  :named typing_Pulse.Spec.GC.Fields.field_offset))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.hd_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(32,4-32,14); use=Pulse.Spec.GC.Fields.fst(32,4-32,14)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Spec.GC.Base.hp_addr)
     (HasType (Pulse.Spec.GC.Fields.hd_address @x0) Pulse.Spec.GC.Base.hp_addr))
    :pattern ((Pulse.Spec.GC.Fields.hd_address @x0))
    :qid typing_Pulse.Spec.GC.Fields.hd_address))
  :named typing_Pulse.Spec.GC.Fields.hd_address))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.is_pointer; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(71,4-71,14); use=Pulse.Spec.GC.Fields.fst(71,4-71,14)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt64.t Dummy_value))
     (HasType (Pulse.Spec.GC.Fields.is_pointer @x0) Prims.bool))
    :pattern ((Pulse.Spec.GC.Fields.is_pointer @x0))
    :qid typing_Pulse.Spec.GC.Fields.is_pointer))
  :named typing_Pulse.Spec.GC.Fields.is_pointer))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.is_pointer_field; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(75,4-75,20); use=Pulse.Spec.GC.Fields.fst(75,4-75,20)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt64.t Dummy_value))
     (HasType (Pulse.Spec.GC.Fields.is_pointer_field @x0) Prims.bool))
    :pattern ((Pulse.Spec.GC.Fields.is_pointer_field @x0))
    :qid typing_Pulse.Spec.GC.Fields.is_pointer_field))
  :named typing_Pulse.Spec.GC.Fields.is_pointer_field))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.well_formed_object; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(83,4-83,22); use=Pulse.Spec.GC.Fields.fst(83,4-83,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Pulse.Spec.GC.Base.heap) (HasType @x1 Pulse.Spec.GC.Base.hp_addr))
     (HasType (Pulse.Spec.GC.Fields.well_formed_object @x0 @x1) Prims.prop))
    :pattern ((Pulse.Spec.GC.Fields.well_formed_object @x0 @x1))
    :qid typing_Pulse.Spec.GC.Fields.well_formed_object))
  :named typing_Pulse.Spec.GC.Fields.well_formed_object))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.wosize; Namespace Pulse.Spec.GC.Fields
(assert
 (! (HasType Pulse.Spec.GC.Fields.wosize (Tm_type U_zero)) :named typing_Pulse.Spec.GC.Fields.wosize))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.edge (Tm_type U_zero)) :named typing_Pulse.Spec.GC.Graph.edge))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.edge_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.edge_list (Tm_type U_zero))
  :named typing_Pulse.Spec.GC.Graph.edge_list))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_id; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.vertex_id (Tm_type U_zero))
  :named typing_Pulse.Spec.GC.Graph.vertex_id))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Heap.read_word; Namespace Pulse.Spec.GC.Heap
(assert
 (! ;; def=Pulse.Spec.GC.Heap.fsti(25,4-25,13); use=Pulse.Spec.GC.Heap.fsti(25,4-25,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Pulse.Spec.GC.Base.heap) (HasType @x1 Pulse.Spec.GC.Base.hp_addr))
     (HasType (Pulse.Spec.GC.Heap.read_word @x0 @x1) (FStar.UInt64.t Dummy_value)))
    :pattern ((Pulse.Spec.GC.Heap.read_word @x0 @x1))
    :qid typing_Pulse.Spec.GC.Heap.read_word))
  :named typing_Pulse.Spec.GC.Heap.read_word))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Object.wosize_of_object; Namespace Pulse.Spec.GC.Object
(assert
 (! ;; def=Pulse.Spec.GC.Object.fsti(106,4-106,20); use=Pulse.Spec.GC.Object.fsti(106,4-106,20)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Pulse.Spec.GC.Base.hp_addr) (HasType @x1 Pulse.Spec.GC.Base.heap))
     (HasType (Pulse.Spec.GC.Object.wosize_of_object @x0 @x1) (FStar.UInt64.t Dummy_value)))
    :pattern ((Pulse.Spec.GC.Object.wosize_of_object @x0 @x1))
    :qid typing_Pulse.Spec.GC.Object.wosize_of_object))
  :named typing_Pulse.Spec.GC.Object.wosize_of_object))
; typing for data constructor proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.T@tok Prims.trivial) :named typing_tok_Prims.T@tok))
; unit inversion
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit))
    :pattern ((HasTypeFuel @u0 @x1 Prims.unit))
    :qid unit_inversion))
  :named unit_inversion))
; unit typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Tm_unit Prims.unit) :named unit_typing))
; well-founded ordering on nat (alt)
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (> (BoxInt_proj_0 @x1) 0)
      (>= (BoxInt_proj_0 @x2) 0)
      (< (BoxInt_proj_0 @x2) (BoxInt_proj_0 @x1)))
     (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x2 @x1)))
    :pattern
     ((HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x2 @x1)))
    :qid well-founded-ordering-on-nat))
  :named well-founded-ordering-on-nat))
(push) ;; push{2
; g : Pulse.Spec.GC.Base.heap (Pulse.Spec.GC.Base.heap)
(declare-fun x_e246fc25c9201731c203dc9e18738560_0 () Term)
; binder_x_e246fc25c9201731c203dc9e18738560_0
;;; Fact-ids: 
(assert
 (! (HasType x_e246fc25c9201731c203dc9e18738560_0 Pulse.Spec.GC.Base.heap)
  :named binder_x_e246fc25c9201731c203dc9e18738560_0))
; src : Pulse.Spec.GC.Base.hp_addr (Pulse.Spec.GC.Base.hp_addr)
(declare-fun x_c39bed69b0e6a97dd42e9a16413dbcb1_1 () Term)
; binder_x_c39bed69b0e6a97dd42e9a16413dbcb1_1
;;; Fact-ids: 
(assert
 (! (HasType x_c39bed69b0e6a97dd42e9a16413dbcb1_1 Pulse.Spec.GC.Base.hp_addr)
  :named binder_x_c39bed69b0e6a97dd42e9a16413dbcb1_1))
; wz : Pulse.Spec.GC.Fields.wosize (Pulse.Spec.GC.Fields.wosize)
(declare-fun x_554e3198ce25a849d5e55a950b1f9de0_2 () Term)
; binder_x_554e3198ce25a849d5e55a950b1f9de0_2
;;; Fact-ids: 
(assert
 (! (HasType x_554e3198ce25a849d5e55a950b1f9de0_2 Pulse.Spec.GC.Fields.wosize)
  :named binder_x_554e3198ce25a849d5e55a950b1f9de0_2))
; idx : FStar.UInt64.t (FStar.UInt64.t)
(declare-fun x_fe73a94f2dd77d31df9370eb9a76c290_3 () Term)
; binder_x_fe73a94f2dd77d31df9370eb9a76c290_3
;;; Fact-ids: 
(assert
 (! (HasType x_fe73a94f2dd77d31df9370eb9a76c290_3 (FStar.UInt64.t Dummy_value))
  :named binder_x_fe73a94f2dd77d31df9370eb9a76c290_3))
(declare-fun Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd (Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
  :named refinement_kinding_Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x2))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
      ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
       (Prims.precedes
        U_zero
        U_zero
        Prims.int
        Prims.int
        (Prims.op_Subtraction (FStar.UInt64.v @x2) (FStar.UInt64.v @x1))
        (Prims.op_Subtraction
         (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2)
         (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x2)))
    :qid refinement_interpretation_Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
  :named refinement_interpretation_Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
; haseq for Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x0)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x0))))
    :qid haseqTm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
  :named haseqTm_refine_ea0d5ab1008d7606ba92186bdbbe82fd))
(declare-fun Pulse.Spec.GC.GraphBridge.collect_edges_from_object (Term Term Term Term) Term)

(declare-fun Tm_refine_342151ed351c78dc8ce598768ff63d17 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_342151ed351c78dc8ce598768ff63d17 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_342151ed351c78dc8ce598768ff63d17))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(31,10-31,19); use=Pulse.Spec.GC.GraphBridge.fst(31,10-31,19)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_342151ed351c78dc8ce598768ff63d17)
     (HasTypeFuel @u0 @x1 Pulse.Spec.GC.Graph.edge_list))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :qid refinement_interpretation_Tm_refine_342151ed351c78dc8ce598768ff63d17))
  :named refinement_interpretation_Tm_refine_342151ed351c78dc8ce598768ff63d17))
; haseq for Tm_refine_342151ed351c78dc8ce598768ff63d17
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_342151ed351c78dc8ce598768ff63d17))
   (Valid (Prims.hasEq U_zero Pulse.Spec.GC.Graph.edge_list)))
  :named haseqTm_refine_342151ed351c78dc8ce598768ff63d17))
; g: Pulse.Spec.GC.Base.heap ->     src: Pulse.Spec.GC.Base.hp_addr ->     wz: Pulse.Spec.GC.Fields.wosize ->     idx:       FStar.UInt64.t         {FStar.UInt64.v wz - FStar.UInt64.v idx << FStar.UInt64.v wz - FStar.UInt64.v idx}   -> Prims.Ghost Pulse.Spec.GC.Graph.edge_list
(declare-fun Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb () Term)
; kinding_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb
;;; Fact-ids: 
(assert
 (! (HasType Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb (Tm_type U_zero))
  :named kinding_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
    :qid Pulse.Spec.GC.GraphBridge_pre_typing_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
  :named Pulse.Spec.GC.GraphBridge_pre_typing_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
; interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb)
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5)
      (forall ((@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
       (! (implies
         (and
          ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
          (Valid
           ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
           (Pulse.Spec.GC.Fields.well_formed_object @x1 @x2))
          ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84)
          (<=
           (BoxInt_proj_0 (FStar.UInt64.v @x3))
           (BoxInt_proj_0 (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x2 @x1))))
          (HasType @x1 Pulse.Spec.GC.Base.heap)
          (HasType @x2 Pulse.Spec.GC.Base.hp_addr)
          (HasType @x3 Pulse.Spec.GC.Fields.wosize)
          (HasType @x4 (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x3)))
         (HasType
          (ApplyTT (ApplyTT (ApplyTT (ApplyTT @x0 @x1) @x2) @x3) @x4)
          Tm_refine_342151ed351c78dc8ce598768ff63d17))
        :pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT @x0 @x1) @x2) @x3) @x4))
        :qid
         Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb.1))
      (IsTotFun @x0)
      ;; def=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5)
      (forall ((@x1 Term))
       (! (implies (HasType @x1 Pulse.Spec.GC.Base.heap) (IsTotFun (ApplyTT @x0 @x1)))
        :pattern ((ApplyTT @x0 @x1))
        :qid
         Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb.2))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5); use=Pulse.Spec.GC.GraphBridge.fst(30,38-57,5)
      (forall ((@x1 Term) (@x2 Term))
       (! (implies
         (and (HasType @x1 Pulse.Spec.GC.Base.heap) (HasType @x2 Pulse.Spec.GC.Base.hp_addr))
         (IsTotFun (ApplyTT (ApplyTT @x0 @x1) @x2)))
        :pattern ((ApplyTT (ApplyTT @x0 @x1) @x2))
        :qid
         Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb.3))))
    :pattern ((HasTypeZ @x0 Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
    :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
  :named Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
(declare-fun Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (ApplyTT
      (ApplyTT
       (ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok @x0) @x1)
       @x2)
      @x3)
     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3))
    :pattern
     ((ApplyTT
       (ApplyTT
        (ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok @x0) @x1)
        @x2)
       @x3))
    :qid token_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
  :named token_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@x0 Term))
   (! (and
     (NoHoist
      @x0
      (HasType
       Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok
       Tm_ghost_arrow_f288117ee369b1fbcd9bed15d8cc66bb))
     ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
     (forall ((@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
      (! (=
        (ApplyTT
         (ApplyTT
          (ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok @x1) @x2)
          @x3)
         @x4)
        (Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x1 @x2 @x3 @x4))
       :pattern ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x1 @x2 @x3 @x4))
       :qid function_token_typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.1)))
    :pattern ((ApplyTT @x0 Pulse.Spec.GC.GraphBridge.collect_edges_from_object@tok))
    :qid function_token_typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
  :named function_token_typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))

; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
       (Pulse.Spec.GC.Fields.well_formed_object @x0 @x1))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84)
      (<=
       (BoxInt_proj_0 (FStar.UInt64.v @x2))
       (BoxInt_proj_0 (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x1 @x0))))
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
      (HasType @x2 Pulse.Spec.GC.Fields.wosize)
      (HasType @x3 (Tm_refine_ea0d5ab1008d7606ba92186bdbbe82fd @x2)))
     (HasType
      (Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3)
      Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :pattern ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3))
    :qid typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
  :named typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
(declare-fun label_18 () Bool)
(declare-fun label_17 () Bool)
(declare-fun label_16 () Bool)
(declare-fun label_15 () Bool)
(declare-fun label_14 () Bool)
(declare-fun label_13 () Bool)
(declare-fun label_12 () Bool)
(declare-fun label_11 () Bool)
(declare-fun label_10 () Bool)
(declare-fun label_9 () Bool)
(declare-fun label_8 () Bool)
(declare-fun label_7 () Bool)
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,26-46,49); use=Pulse.Spec.GC.GraphBridge.fst(36,36-36,41)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0)
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.edge))
      ;; def=FStar.Seq.Base.fsti(46,37-46,47); use=Pulse.Spec.GC.GraphBridge.fst(36,36-36,41)
      (= (FStar.Seq.Base.length U_zero Pulse.Spec.GC.Graph.edge @x1) (BoxInt 0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
    :qid refinement_interpretation_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
  :named refinement_interpretation_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
; haseq for Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
   (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.edge))))
  :named haseqTm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
(declare-fun Tm_refine_0405ada811d3efc55877fd841a8080a6 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_0405ada811d3efc55877fd841a8080a6 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_0405ada811d3efc55877fd841a8080a6))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_0405ada811d3efc55877fd841a8080a6)
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
      ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
       (Prims.precedes
        U_zero
        U_zero
        Prims.int
        Prims.int
        (Prims.op_Subtraction
         (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2)
         (FStar.UInt64.v @x1))
        (Prims.op_Subtraction
         (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2)
         (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_0405ada811d3efc55877fd841a8080a6))
    :qid refinement_interpretation_Tm_refine_0405ada811d3efc55877fd841a8080a6))
  :named refinement_interpretation_Tm_refine_0405ada811d3efc55877fd841a8080a6))
; haseq for Tm_refine_0405ada811d3efc55877fd841a8080a6
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_0405ada811d3efc55877fd841a8080a6))
   (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
  :named haseqTm_refine_0405ada811d3efc55877fd841a8080a6))
; Encoding query formula : (forall (p: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;     Pulse.Spec.GC.Fields.well_formed_object g src /\
;     FStar.UInt64.v wz <= FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object src g) /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list). Prims.auto_squash (p ghost_result)) ==>
;     (forall (k: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;         (forall (x: Pulse.Spec.GC.Graph.edge_list). {:pattern Prims.guard_free (k x)}
;             (x ==
;               (match FStar.UInt64.v idx >= FStar.UInt64.v wz with
;                 | true -> seq![]
;                 | _ ->
;                   (match
;                       Pulse.Spec.GC.Fields.is_pointer_field (Pulse.Spec.GC.Heap.read_word g
;                             (Pulse.Spec.GC.Fields.field_address src idx)) &&
;                       Pulse.Spec.GC.Heap.read_word g (Pulse.Spec.GC.Fields.field_address src idx) <>
;                       (0uL <: FStar.UInt64.t)
;                     with
;                     | true ->
;                       FStar.Seq.Base.cons (src,
;                         Pulse.Spec.GC.Heap.read_word g (Pulse.Spec.GC.Fields.field_address src idx))
;                         (Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                             src
;                             wz
;                             (FStar.UInt64.add idx (1uL <: FStar.UInt64.t)))
;                     | _ ->
;                       Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                         src
;                         wz
;                         (FStar.UInt64.add idx (1uL <: FStar.UInt64.t)))
;                   <:
;                   Pulse.Spec.GC.Graph.edge_list) ==>
;               (forall (return_val: Pulse.Spec.GC.Graph.edge_list). return_val == x ==> p return_val)
;             ) ==>
;             k x) ==>
;         (FStar.UInt64.v idx >= FStar.UInt64.v wz == true ==>
;           (forall (return_val:
;               s: FStar.Seq.Base.seq Pulse.Spec.GC.Graph.edge {FStar.Seq.Base.length s = 0}).
;               return_val == seq![] ==> k return_val)) /\
;         (~(FStar.UInt64.v idx >= FStar.UInt64.v wz = true) ==>
;           (forall (b: Prims.bool).
;               FStar.UInt64.v idx >= FStar.UInt64.v wz == b ==>
;               (forall (pure_result: Prims.unit).
;                   Prims.pow2 54 < Prims.pow2 61 ==>
;                   FStar.UInt64.v wz < Prims.pow2 54 /\
;                   (forall (pure_result: Prims.unit).
;                       FStar.UInt64.v wz < Prims.pow2 54 ==>
;                       FStar.UInt64.v idx < FStar.UInt64.v wz /\
;                       (forall (pure_result: Prims.unit).
;                           FStar.UInt64.v idx < FStar.UInt64.v wz ==>
;                           FStar.UInt64.v idx < Prims.pow2 54 /\
;                           (forall (pure_result: Prims.unit).
;                               FStar.UInt64.v idx < Prims.pow2 54 ==>
;                               FStar.UInt64.v idx < Prims.pow2 61 /\
;                               (forall (pure_result: Prims.unit).
;                                   FStar.UInt64.v idx < Prims.pow2 61 ==>
;                                   FStar.UInt64.v src + FStar.UInt64.v idx * 8 <
;                                   Pulse.Spec.GC.Base.heap_size /\
;                                   (forall (pure_result: Prims.unit).
;                                       FStar.UInt64.v src + FStar.UInt64.v idx * 8 <
;                                       Pulse.Spec.GC.Base.heap_size ==>
;                                       FStar.UInt64.v idx < Prims.pow2 61 /\
;                                       (forall (any_result: FStar.UInt64.t).
;                                           idx == any_result ==>
;                                           FStar.UInt64.v src + FStar.UInt64.v idx * 8 <
;                                           Pulse.Spec.GC.Base.heap_size /\
;                                           (forall (pure_result: Pulse.Spec.GC.Base.hp_addr).
;                                               FStar.UInt64.v pure_result =
;                                               FStar.UInt64.v src + FStar.UInt64.v idx * 8 ==>
;                                               Pulse.Spec.GC.Fields.field_address src idx ==
;                                               pure_result ==>
;                                               FStar.UInt.size (FStar.UInt64.v idx + 1) 64 /\
;                                               (forall (pure_result: FStar.UInt64.t).
;                                                   FStar.UInt64.v idx + 1 =
;                                                   FStar.UInt64.v pure_result ==>
;                                                   FStar.UInt64.add idx (1uL <: FStar.UInt64.t) ==
;                                                   pure_result ==>
;                                                   FStar.UInt64.v wz -
;                                                   FStar.UInt64.v (FStar.UInt64.add idx
;                                                         (1uL <: FStar.UInt64.t)) <<
;                                                   FStar.UInt64.v wz - FStar.UInt64.v idx /\
;                                                   (forall (return_val:
;                                                       idx:
;                                                       FStar.UInt64.t
;                                                         { FStar.UInt64.v wz - FStar.UInt64.v idx <<
;                                                           FStar.UInt64.v wz - FStar.UInt64.v idx }).
;                                                       return_val ==
;                                                       FStar.UInt64.add idx (1uL <: FStar.UInt64.t) ==>
;                                                       FStar.UInt64.add idx (1uL <: FStar.UInt64.t) ==
;                                                       return_val ==>
;                                                       Pulse.Spec.GC.Fields.well_formed_object g src /\
;                                                       FStar.UInt64.v wz <=
;                                                       FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object
;                                                             src
;                                                             g) /\
;                                                       (forall (ghost_result:
;                                                           Pulse.Spec.GC.Graph.edge_list).
;                                                           Pulse.Spec.GC.GraphBridge.collect_edges_from_object
;                                                             g
;                                                             src
;                                                             wz
;                                                             (FStar.UInt64.add idx
;                                                                 (1uL <: FStar.UInt64.t)) ==
;                                                           ghost_result ==>
;                                                           (forall (k:
;                                                               Prims.pure_post Pulse.Spec.GC.Graph.edge_list
;                                                               ).
;                                                               (forall (x:
;                                                                   Pulse.Spec.GC.Graph.edge_list).
;                                                                   {:pattern Prims.guard_free (k x)}
;                                                                   k x ==> k x) ==>
;                                                               ((Pulse.Spec.GC.Fields.is_pointer_field
;                                                                   (Pulse.Spec.GC.Heap.read_word g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx)) &&
;                                                                 Pulse.Spec.GC.Heap.read_word g
;                                                                   (Pulse.Spec.GC.Fields.field_address
;                                                                       src
;                                                                       idx) <>
;                                                                 (0uL <: FStar.UInt64.t)) ==
;                                                                 true ==>
;                                                                 FStar.UInt64.v (Pulse.Spec.GC.Heap.read_word
;                                                                       g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx)) >=
;                                                                 0 /\
;                                                                 FStar.UInt64.v (Pulse.Spec.GC.Heap.read_word
;                                                                       g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx)) <
;                                                                 Pulse.Spec.GC.Base.heap_size /\
;                                                                 FStar.UInt64.v (Pulse.Spec.GC.Heap.read_word
;                                                                       g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx)) %
;                                                                 FStar.UInt64.v Pulse.Spec.GC.Base.mword
;                                                                  ==
;                                                                 0 /\
;                                                                 (forall (any_result: FStar.UInt64.t)
;                                                                   .
;                                                                     Pulse.Spec.GC.Heap.read_word g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx) ==
;                                                                     any_result ==>
;                                                                     (forall (any_result:
;                                                                         Pulse.Spec.GC.Graph.edge_list)
;                                                                       .
;                                                                         k any_result))) /\
;                                                               (~((Pulse.Spec.GC.Fields.is_pointer_field
;                                                                     (Pulse.Spec.GC.Heap.read_word g
;                                                                         (Pulse.Spec.GC.Fields.field_address
;                                                                             src
;                                                                             idx)) &&
;                                                                   Pulse.Spec.GC.Heap.read_word g
;                                                                     (Pulse.Spec.GC.Fields.field_address
;                                                                         src
;                                                                         idx) <>
;                                                                   (0uL <: FStar.UInt64.t)) =
;                                                                   true) ==>
;                                                                 (forall (b: Prims.bool).
;                                                                     (Pulse.Spec.GC.Fields.is_pointer_field
;                                                                       (Pulse.Spec.GC.Heap.read_word g
;                                                                           (Pulse.Spec.GC.Fields.field_address
;                                                                               src
;                                                                               idx)) &&
;                                                                     Pulse.Spec.GC.Heap.read_word g
;                                                                       (Pulse.Spec.GC.Fields.field_address
;                                                                           src
;                                                                           idx) <>
;                                                                     (0uL <: FStar.UInt64.t)) ==
;                                                                     b ==>
;                                                                     (forall (any_result:
;                                                                         Pulse.Spec.GC.Graph.edge_list)
;                                                                       .
;                                                                         k any_result))))))))))))))))
;         ))) /\
; (forall (p: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;     Pulse.Spec.GC.Fields.well_formed_object g src /\
;     FStar.UInt64.v wz <= FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object src g) /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list). Prims.auto_squash (p ghost_result)) ==>
;     Pulse.Spec.GC.Fields.well_formed_object g src /\
;     FStar.UInt64.v wz <= FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object src g) /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list).
;         ghost_result ==
;         (match FStar.UInt64.v idx >= FStar.UInt64.v wz with
;           | true -> seq![]
;           | _ ->
;             (match
;                 Pulse.Spec.GC.Fields.is_pointer_field (Pulse.Spec.GC.Heap.read_word g
;                       (Pulse.Spec.GC.Fields.field_address src idx)) &&
;                 Pulse.Spec.GC.Heap.read_word g (Pulse.Spec.GC.Fields.field_address src idx) <>
;                 (0uL <: FStar.UInt64.t)
;               with
;               | true ->
;                 FStar.Seq.Base.cons (src,
;                   Pulse.Spec.GC.Heap.read_word g (Pulse.Spec.GC.Fields.field_address src idx))
;                   (Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                       src
;                       wz
;                       (FStar.UInt64.add idx (1uL <: FStar.UInt64.t)))
;               | _ ->
;                 Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                   src
;                   wz
;                   (FStar.UInt64.add idx (1uL <: FStar.UInt64.t)))
;             <:
;             Pulse.Spec.GC.Graph.edge_list) ==>
;         (forall (return_val: Pulse.Spec.GC.Graph.edge_list).
;             return_val == ghost_result ==> p return_val)))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec collect_edges_from_object`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=Prims.fst(414,51-414,91); use=Prims.fst(438,19-438,32)
   (and
    ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
    (forall ((@x0 Term))
     (! (implies
       (and
        (HasType @x0 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
         (Pulse.Spec.GC.Fields.well_formed_object
          x_e246fc25c9201731c203dc9e18738560_0
          x_c39bed69b0e6a97dd42e9a16413dbcb1_1))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (<=
         (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
         (BoxInt_proj_0
          (FStar.UInt64.v
           (Pulse.Spec.GC.Object.wosize_of_object
            x_c39bed69b0e6a97dd42e9a16413dbcb1_1
            x_e246fc25c9201731c203dc9e18738560_0))))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (forall ((@x1 Term))
         (! (implies
           (or label_1 (HasType @x1 Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
           (Valid
            ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (ApplyTT @x0 @x1)))
          :pattern
           (;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (Valid
             ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
             (ApplyTT @x0 @x1)))
          :qid @query.1)))
       ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
       (forall ((@x1 Term))
        (! (implies
          (and
           (HasType @x1 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
           (forall ((@x2 Term))
            (! (implies
              (implies
               ;; def=Pulse.Spec.GC.GraphBridge.fst(31,10-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
               (=
                @x2
                (let
                  ((@lb3
                    (Prims.op_GreaterThanOrEqual
                     (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                     (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))))
                 (ite
                  (= @lb3 (BoxBool true))
                  (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)
                  (let
                    ((@lb4
                      (Prims.op_AmpAmp
                       (Pulse.Spec.GC.Fields.is_pointer_field
                        (Pulse.Spec.GC.Heap.read_word
                         x_e246fc25c9201731c203dc9e18738560_0
                         (Pulse.Spec.GC.Fields.field_address
                          x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                          x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                       (Prims.op_disEquality
                        (FStar.UInt64.t Dummy_value)
                        (Pulse.Spec.GC.Heap.read_word
                         x_e246fc25c9201731c203dc9e18738560_0
                         (Pulse.Spec.GC.Fields.field_address
                          x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                          x_fe73a94f2dd77d31df9370eb9a76c290_3))
                        (FStar.UInt64.uint_to_t (BoxInt 0))))))
                   (ite
                    (= @lb4 (BoxBool true))
                    (FStar.Seq.Base.cons
                     U_zero
                     Pulse.Spec.GC.Graph.edge
                     (FStar.Pervasives.Native.Mktuple2
                      U_zero
                      U_zero
                      Pulse.Spec.GC.Graph.vertex_id
                      Pulse.Spec.GC.Graph.vertex_id
                      x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                      (Pulse.Spec.GC.Heap.read_word
                       x_e246fc25c9201731c203dc9e18738560_0
                       (Pulse.Spec.GC.Fields.field_address
                        x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                        x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                      x_e246fc25c9201731c203dc9e18738560_0
                      x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                      x_554e3198ce25a849d5e55a950b1f9de0_2
                      (FStar.UInt64.add
                       x_fe73a94f2dd77d31df9370eb9a76c290_3
                       (FStar.UInt64.uint_to_t (BoxInt 1)))))
                    (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                     x_e246fc25c9201731c203dc9e18738560_0
                     x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                     x_554e3198ce25a849d5e55a950b1f9de0_2
                     (FStar.UInt64.add
                      x_fe73a94f2dd77d31df9370eb9a76c290_3
                      (FStar.UInt64.uint_to_t (BoxInt 1)))))))))
               ;; def=Prims.fst(364,2-364,58); use=Prims.fst(434,19-434,31)
               (forall ((@x3 Term))
                (! (implies
                  (and
                   (HasType @x3 Pulse.Spec.GC.Graph.edge_list)
                   ;; def=Prims.fst(364,26-364,41); use=Prims.fst(434,19-434,31)
                   (= @x3 @x2))
                  ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
                  (Valid
                   ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
                   (ApplyTT @x0 @x3)))
                 :qid @query.4)))
              ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
              (Valid
               ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
               (ApplyTT @x1 @x2)))
             :weight 0
             :pattern ((ApplyTT @x1 @x2))
             :qid @query.3)))
          ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
          (and
           (implies
            ;; def=Pulse.Spec.GC.GraphBridge.fst(36,5-36,26); use=Pulse.Spec.GC.GraphBridge.fst(36,5-36,26)
            (=
             (Prims.op_GreaterThanOrEqual
              (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
              (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
             (BoxBool true))
            ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (forall ((@x2 Term))
             (! (implies
               (and
                (HasType @x2 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0)
                ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                (= @x2 (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)))
               ;; def=Prims.fst(364,46-364,58); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
               (Valid
                ;; def=Prims.fst(364,46-364,58); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                (ApplyTT @x1 @x2)))
              :qid @query.5)))
           (implies
            ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (not
             ;; def=Pulse.Spec.GC.GraphBridge.fst(36,5-36,26); use=Pulse.Spec.GC.GraphBridge.fst(36,5-36,26)
             (=
              (Prims.op_GreaterThanOrEqual
               (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
               (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
              (BoxBool true)))
            ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (forall ((@x2 Term))
             (! (implies
               (and
                (HasType @x2 Prims.bool)
                ;; def=Pulse.Spec.GC.GraphBridge.fst(36,5-56,10); use=Pulse.Spec.GC.GraphBridge.fst(36,5-56,10)
                (=
                 (Prims.op_GreaterThanOrEqual
                  (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                  (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
                 @x2))
               ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(38,22-38,36)
               (forall ((@x3 Term))
                (! (implies
                  (and
                   (HasType @x3 Prims.unit)
                   ;; def=FStar.Math.Lemmas.fsti(148,12-148,29); use=Pulse.Spec.GC.GraphBridge.fst(38,22-38,36)
                   (<
                    (BoxInt_proj_0 (Prims.pow2 (BoxInt 54)))
                    (BoxInt_proj_0 (Prims.pow2 (BoxInt 61)))))
                  ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(39,4-39,10)
                  (and
                   ;; def=Pulse.Spec.GC.GraphBridge.fst(39,11-39,31); use=Pulse.Spec.GC.GraphBridge.fst(39,4-39,10)
                   (or
                    label_2
                    ;; def=Pulse.Spec.GC.GraphBridge.fst(39,11-39,31); use=Pulse.Spec.GC.GraphBridge.fst(39,4-39,10)
                    (<
                     (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
                     (BoxInt_proj_0 (Prims.pow2 (BoxInt 54)))))
                   ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(39,4-39,10)
                   (forall ((@x4 Term))
                    (! (implies
                      (and
                       (HasType @x4 Prims.unit)
                       ;; def=Pulse.Spec.GC.GraphBridge.fst(39,11-39,31); use=Pulse.Spec.GC.GraphBridge.fst(39,4-39,10)
                       (<
                        (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
                        (BoxInt_proj_0 (Prims.pow2 (BoxInt 54)))))
                      ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(40,4-40,10)
                      (and
                       ;; def=Pulse.Spec.GC.GraphBridge.fst(40,11-40,33); use=Pulse.Spec.GC.GraphBridge.fst(40,4-40,10)
                       (or
                        label_3
                        ;; def=Pulse.Spec.GC.GraphBridge.fst(40,11-40,33); use=Pulse.Spec.GC.GraphBridge.fst(40,4-40,10)
                        (<
                         (BoxInt_proj_0 (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                         (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))))
                       ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(40,4-40,10)
                       (forall ((@x5 Term))
                        (! (implies
                          (and
                           (HasType @x5 Prims.unit)
                           ;; def=Pulse.Spec.GC.GraphBridge.fst(40,11-40,33); use=Pulse.Spec.GC.GraphBridge.fst(40,4-40,10)
                           (<
                            (BoxInt_proj_0 (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                            (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))))
                          ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(41,4-41,10)
                          (and
                           ;; def=Pulse.Spec.GC.GraphBridge.fst(41,11-41,32); use=Pulse.Spec.GC.GraphBridge.fst(41,4-41,10)
                           (or
                            label_4
                            ;; def=Pulse.Spec.GC.GraphBridge.fst(41,11-41,32); use=Pulse.Spec.GC.GraphBridge.fst(41,4-41,10)
                            (<
                             (BoxInt_proj_0 (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                             (BoxInt_proj_0 (Prims.pow2 (BoxInt 54)))))
                           ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(41,4-41,10)
                           (forall ((@x6 Term))
                            (! (implies
                              (and
                               (HasType @x6 Prims.unit)
                               ;; def=Pulse.Spec.GC.GraphBridge.fst(41,11-41,32); use=Pulse.Spec.GC.GraphBridge.fst(41,4-41,10)
                               (<
                                (BoxInt_proj_0 (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                (BoxInt_proj_0 (Prims.pow2 (BoxInt 54)))))
                              ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(42,4-42,10)
                              (and
                               ;; def=Pulse.Spec.GC.GraphBridge.fst(42,11-42,32); use=Pulse.Spec.GC.GraphBridge.fst(42,4-42,10)
                               (or
                                label_5
                                ;; def=Pulse.Spec.GC.GraphBridge.fst(42,11-42,32); use=Pulse.Spec.GC.GraphBridge.fst(42,4-42,10)
                                (<
                                 (BoxInt_proj_0
                                  (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                 (BoxInt_proj_0 (Prims.pow2 (BoxInt 61)))))
                               ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(42,4-42,10)
                               (forall ((@x7 Term))
                                (! (implies
                                  (and
                                   (HasType @x7 Prims.unit)
                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(42,11-42,32); use=Pulse.Spec.GC.GraphBridge.fst(42,4-42,10)
                                   (<
                                    (BoxInt_proj_0
                                     (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                    (BoxInt_proj_0 (Prims.pow2 (BoxInt 61)))))
                                  ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(45,4-45,10)
                                  (and
                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(45,11-45,62); use=Pulse.Spec.GC.GraphBridge.fst(45,4-45,10)
                                   (or
                                    label_6
                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(45,11-45,62); use=Pulse.Spec.GC.GraphBridge.fst(45,4-45,10)
                                    (<
                                     (BoxInt_proj_0
                                      (Prims.op_Addition
                                       (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_1)
                                       (Prims.op_Multiply
                                        (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                        (BoxInt 8))))
                                     (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                   ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(45,4-45,10)
                                   (forall ((@x8 Term))
                                    (! (implies
                                      (and
                                       (HasType @x8 Prims.unit)
                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(45,11-45,62); use=Pulse.Spec.GC.GraphBridge.fst(45,4-45,10)
                                       (<
                                        (BoxInt_proj_0
                                         (Prims.op_Addition
                                          (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_1)
                                          (Prims.op_Multiply
                                           (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                           (BoxInt 8))))
                                        (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                      ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                      (and
                                       ;; def=Pulse.Spec.GC.Fields.fst(58,56-58,81); use=Pulse.Spec.GC.GraphBridge.fst(46,39-46,42)
                                       (or
                                        label_7
                                        ;; def=Pulse.Spec.GC.Fields.fst(58,56-58,81); use=Pulse.Spec.GC.GraphBridge.fst(46,39-46,42)
                                        (<
                                         (BoxInt_proj_0
                                          (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                         (BoxInt_proj_0 (Prims.pow2 (BoxInt 61)))))
                                       ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                       (forall ((@x9 Term))
                                        (! (implies
                                          (and
                                           (HasType @x9 (FStar.UInt64.t Dummy_value))
                                           ;; def=Pulse.Spec.GC.Fields.fst(58,39-58,48); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                           (= x_fe73a94f2dd77d31df9370eb9a76c290_3 @x9))
                                          ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(46,21-46,34)
                                          (and
                                           ;; def=Pulse.Spec.GC.Fields.fst(60,14-60,74); use=Pulse.Spec.GC.GraphBridge.fst(46,21-46,34)
                                           (or
                                            label_8
                                            ;; def=Pulse.Spec.GC.Fields.fst(60,14-60,74); use=Pulse.Spec.GC.GraphBridge.fst(46,21-46,34)
                                            (<
                                             (BoxInt_proj_0
                                              (Prims.op_Addition
                                               (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_1)
                                               (Prims.op_Multiply
                                                (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                                (BoxInt 8))))
                                             (BoxInt_proj_0
                                              (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                           ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(46,21-46,34)
                                           (forall ((@x10 Term))
                                            (! (implies
                                              (and
                                               (HasType @x10 Pulse.Spec.GC.Base.hp_addr)
                                               ;; def=Pulse.Spec.GC.Fields.fst(61,22-61,80); use=Pulse.Spec.GC.GraphBridge.fst(46,21-46,34)
                                               (=
                                                (FStar.UInt64.v @x10)
                                                (Prims.op_Addition
                                                 (FStar.UInt64.v
                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_1)
                                                 (Prims.op_Multiply
                                                  (FStar.UInt64.v
                                                   x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                                  (BoxInt 8))))
                                               ;; def=Pulse.Spec.GC.GraphBridge.fst(46,8-46,42); use=Pulse.Spec.GC.GraphBridge.fst(46,8-46,42)
                                               (=
                                                (Pulse.Spec.GC.Fields.field_address
                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                 x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                                @x10))
                                              ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                              (and
                                               ;; def=FStar.UInt64.fsti(89,12-89,32); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                               (or
                                                label_9
                                                ;; def=FStar.UInt64.fsti(89,12-89,32); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                                (Valid
                                                 ;; def=FStar.UInt64.fsti(89,12-89,32); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                                 (FStar.UInt.size
                                                  (Prims.op_Addition
                                                   (FStar.UInt64.v
                                                    x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                                   (BoxInt 1))
                                                  (BoxInt 64))))
                                               ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                               (forall ((@x11 Term))
                                                (! (implies
                                                  (and
                                                   (HasType @x11 (FStar.UInt64.t Dummy_value))
                                                   ;; def=FStar.UInt64.fsti(90,21-90,36); use=Pulse.Spec.GC.GraphBridge.fst(48,55-48,58)
                                                   (=
                                                    (Prims.op_Addition
                                                     (FStar.UInt64.v
                                                      x_fe73a94f2dd77d31df9370eb9a76c290_3)
                                                     (BoxInt 1))
                                                    (FStar.UInt64.v @x11))
                                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                   (=
                                                    (FStar.UInt64.add
                                                     x_fe73a94f2dd77d31df9370eb9a76c290_3
                                                     (FStar.UInt64.uint_to_t (BoxInt 1)))
                                                    @x11))
                                                  ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                  (and
                                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,50-48,67)
                                                   (or
                                                    label_10
                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,50-48,67)
                                                    (Valid
                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(48,50-48,67)
                                                     (Prims.precedes
                                                      U_zero
                                                      U_zero
                                                      Prims.int
                                                      Prims.int
                                                      (Prims.op_Subtraction
                                                       (FStar.UInt64.v
                                                        x_554e3198ce25a849d5e55a950b1f9de0_2)
                                                       (FStar.UInt64.v
                                                        (FStar.UInt64.add
                                                         x_fe73a94f2dd77d31df9370eb9a76c290_3
                                                         (FStar.UInt64.uint_to_t (BoxInt 1)))))
                                                      (Prims.op_Subtraction
                                                       (FStar.UInt64.v
                                                        x_554e3198ce25a849d5e55a950b1f9de0_2)
                                                       (FStar.UInt64.v
                                                        x_fe73a94f2dd77d31df9370eb9a76c290_3)))))
                                                   ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                   (forall ((@x12 Term))
                                                    (! (implies
                                                      (and
                                                       (HasType
                                                        @x12
                                                        Tm_refine_0405ada811d3efc55877fd841a8080a6)
                                                       ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                       (=
                                                        @x12
                                                        (FStar.UInt64.add
                                                         x_fe73a94f2dd77d31df9370eb9a76c290_3
                                                         (FStar.UInt64.uint_to_t (BoxInt 1))))
                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(30,73-48,67); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                       (=
                                                        (FStar.UInt64.add
                                                         x_fe73a94f2dd77d31df9370eb9a76c290_3
                                                         (FStar.UInt64.uint_to_t (BoxInt 1)))
                                                        @x12))
                                                      ;; def=Prims.fst(493,29-493,100); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                      (and
                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                       (or
                                                        label_11
                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                        (Valid
                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                         (Pulse.Spec.GC.Fields.well_formed_object
                                                          x_e246fc25c9201731c203dc9e18738560_0
                                                          x_c39bed69b0e6a97dd42e9a16413dbcb1_1)))
                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                       (or
                                                        label_12
                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                        (<=
                                                         (BoxInt_proj_0
                                                          (FStar.UInt64.v
                                                           x_554e3198ce25a849d5e55a950b1f9de0_2))
                                                         (BoxInt_proj_0
                                                          (FStar.UInt64.v
                                                           (Pulse.Spec.GC.Object.wosize_of_object
                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                            x_e246fc25c9201731c203dc9e18738560_0)))))
                                                       ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(48,15-48,40)
                                                       (forall ((@x13 Term))
                                                        (! (implies
                                                          (and
                                                           (HasType
                                                            @x13
                                                            Pulse.Spec.GC.Graph.edge_list)
                                                           ;; def=Pulse.Spec.GC.GraphBridge.fst(48,8-48,67); use=Pulse.Spec.GC.GraphBridge.fst(48,8-48,67)
                                                           (=
                                                            (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                                                             x_e246fc25c9201731c203dc9e18738560_0
                                                             x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                             x_554e3198ce25a849d5e55a950b1f9de0_2
                                                             (FStar.UInt64.add
                                                              x_fe73a94f2dd77d31df9370eb9a76c290_3
                                                              (FStar.UInt64.uint_to_t (BoxInt 1))))
                                                            @x13))
                                                          ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                          (forall ((@x14 Term))
                                                           (! (implies
                                                             (and
                                                              (HasType
                                                               @x14
                                                               (Prims.pure_post
                                                                U_zero
                                                                Pulse.Spec.GC.Graph.edge_list))
                                                              ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                              (forall ((@x15 Term))
                                                               (! (implies
                                                                 ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                 (Valid
                                                                  ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                  (ApplyTT @x1 @x15))
                                                                 ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                 (Valid
                                                                  ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                  (ApplyTT @x14 @x15)))
                                                                :weight 0
                                                                :pattern ((ApplyTT @x14 @x15))
                                                                :qid @query.19)))
                                                             ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                             (and
                                                              (implies
                                                               ;; def=Pulse.Spec.GC.GraphBridge.fst(50,7-50,53); use=Pulse.Spec.GC.GraphBridge.fst(50,7-50,53)
                                                               (=
                                                                (Prims.op_AmpAmp
                                                                 (Pulse.Spec.GC.Fields.is_pointer_field
                                                                  (Pulse.Spec.GC.Heap.read_word
                                                                   x_e246fc25c9201731c203dc9e18738560_0
                                                                   (Pulse.Spec.GC.Fields.field_address
                                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                    x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                                                                 (Prims.op_disEquality
                                                                  (FStar.UInt64.t Dummy_value)
                                                                  (Pulse.Spec.GC.Heap.read_word
                                                                   x_e246fc25c9201731c203dc9e18738560_0
                                                                   (Pulse.Spec.GC.Fields.field_address
                                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                    x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                                                  (FStar.UInt64.uint_to_t (BoxInt 0))))
                                                                (BoxBool true))
                                                               ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                               (and
                                                                ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                (or
                                                                 label_13
                                                                 ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                 (>=
                                                                  (BoxInt_proj_0
                                                                   (FStar.UInt64.v
                                                                    (Pulse.Spec.GC.Heap.read_word
                                                                     x_e246fc25c9201731c203dc9e18738560_0
                                                                     (Pulse.Spec.GC.Fields.field_address
                                                                      x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                      x_fe73a94f2dd77d31df9370eb9a76c290_3))))
                                                                  (BoxInt_proj_0 (BoxInt 0))))
                                                                ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                (or
                                                                 label_14
                                                                 ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                 (<
                                                                  (BoxInt_proj_0
                                                                   (FStar.UInt64.v
                                                                    (Pulse.Spec.GC.Heap.read_word
                                                                     x_e246fc25c9201731c203dc9e18738560_0
                                                                     (Pulse.Spec.GC.Fields.field_address
                                                                      x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                      x_fe73a94f2dd77d31df9370eb9a76c290_3))))
                                                                  (BoxInt_proj_0
                                                                   (Pulse.Spec.GC.Base.heap_size
                                                                    Dummy_value))))
                                                                ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                (or
                                                                 label_15
                                                                 ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(53,26-53,35)
                                                                 (=
                                                                  (Prims.op_Modulus
                                                                   (FStar.UInt64.v
                                                                    (Pulse.Spec.GC.Heap.read_word
                                                                     x_e246fc25c9201731c203dc9e18738560_0
                                                                     (Pulse.Spec.GC.Fields.field_address
                                                                      x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                      x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                                                                   (FStar.UInt64.v
                                                                    (Pulse.Spec.GC.Base.mword
                                                                     Dummy_value)))
                                                                  (BoxInt 0)))
                                                                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                (forall ((@x15 Term))
                                                                 (! (implies
                                                                   (and
                                                                    (HasType
                                                                     @x15
                                                                     (FStar.UInt64.t Dummy_value))
                                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(47,8-53,13); use=Pulse.Spec.GC.GraphBridge.fst(53,10-53,35)
                                                                    (=
                                                                     (Pulse.Spec.GC.Heap.read_word
                                                                      x_e246fc25c9201731c203dc9e18738560_0
                                                                      (Pulse.Spec.GC.Fields.field_address
                                                                       x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                       x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                                                     @x15))
                                                                   ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                   (forall ((@x16 Term))
                                                                    (! (implies
                                                                      (HasType
                                                                       @x16
                                                                       Pulse.Spec.GC.Graph.edge_list)
                                                                      ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                      (Valid
                                                                       ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                       (ApplyTT @x14 @x16)))
                                                                     :qid @query.21)))
                                                                  :qid @query.20))))
                                                              (implies
                                                               ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                               (not
                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(50,7-50,53); use=Pulse.Spec.GC.GraphBridge.fst(50,7-50,53)
                                                                (=
                                                                 (Prims.op_AmpAmp
                                                                  (Pulse.Spec.GC.Fields.is_pointer_field
                                                                   (Pulse.Spec.GC.Heap.read_word
                                                                    x_e246fc25c9201731c203dc9e18738560_0
                                                                    (Pulse.Spec.GC.Fields.field_address
                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                     x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                                                                  (Prims.op_disEquality
                                                                   (FStar.UInt64.t Dummy_value)
                                                                   (Pulse.Spec.GC.Heap.read_word
                                                                    x_e246fc25c9201731c203dc9e18738560_0
                                                                    (Pulse.Spec.GC.Fields.field_address
                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                     x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                                                   (FStar.UInt64.uint_to_t
                                                                    (BoxInt 0))))
                                                                 (BoxBool true)))
                                                               ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                               (forall ((@x15 Term))
                                                                (! (implies
                                                                  (and
                                                                   (HasType @x15 Prims.bool)
                                                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(50,7-56,10); use=Pulse.Spec.GC.GraphBridge.fst(50,7-56,10)
                                                                   (=
                                                                    (Prims.op_AmpAmp
                                                                     (Pulse.Spec.GC.Fields.is_pointer_field
                                                                      (Pulse.Spec.GC.Heap.read_word
                                                                       x_e246fc25c9201731c203dc9e18738560_0
                                                                       (Pulse.Spec.GC.Fields.field_address
                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                        x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                                                                     (Prims.op_disEquality
                                                                      (FStar.UInt64.t Dummy_value)
                                                                      (Pulse.Spec.GC.Heap.read_word
                                                                       x_e246fc25c9201731c203dc9e18738560_0
                                                                       (Pulse.Spec.GC.Fields.field_address
                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                                                                        x_fe73a94f2dd77d31df9370eb9a76c290_3))
                                                                      (FStar.UInt64.uint_to_t
                                                                       (BoxInt 0))))
                                                                    @x15))
                                                                  ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                  (forall ((@x16 Term))
                                                                   (! (implies
                                                                     (HasType
                                                                      @x16
                                                                      Pulse.Spec.GC.Graph.edge_list)
                                                                     ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                     (Valid
                                                                      ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
                                                                      (ApplyTT @x14 @x16)))
                                                                    :qid @query.23)))
                                                                 :qid @query.22)))))
                                                            :qid @query.18)))
                                                         :qid @query.17))))
                                                     :qid @query.16))))
                                                 :qid @query.15))))
                                             :qid @query.14))))
                                         :qid @query.13))))
                                     :qid @query.12))))
                                 :qid @query.11))))
                             :qid @query.10))))
                         :qid @query.9))))
                     :qid @query.8))))
                 :qid @query.7)))
              :qid @query.6)))))
         :qid @query.2)))
      :qid @query))
    ;; def=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
    (forall ((@x0 Term))
     (! (implies
       (and
        (HasType @x0 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
         (Pulse.Spec.GC.Fields.well_formed_object
          x_e246fc25c9201731c203dc9e18738560_0
          x_c39bed69b0e6a97dd42e9a16413dbcb1_1))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (<=
         (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
         (BoxInt_proj_0
          (FStar.UInt64.v
           (Pulse.Spec.GC.Object.wosize_of_object
            x_c39bed69b0e6a97dd42e9a16413dbcb1_1
            x_e246fc25c9201731c203dc9e18738560_0))))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (forall ((@x1 Term))
         (! (implies
           (or label_16 (HasType @x1 Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
           (Valid
            ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (ApplyTT @x0 @x1)))
          :pattern
           (;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (Valid
             ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
             (ApplyTT @x0 @x1)))
          :qid @query.25)))
       ;; def=Prims.fst(493,29-493,100); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
       (and
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (or
         label_17
         ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
         (Valid
          ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
          (Pulse.Spec.GC.Fields.well_formed_object
           x_e246fc25c9201731c203dc9e18738560_0
           x_c39bed69b0e6a97dd42e9a16413dbcb1_1)))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (or
         label_18
         ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
         (<=
          (BoxInt_proj_0 (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))
          (BoxInt_proj_0
           (FStar.UInt64.v
            (Pulse.Spec.GC.Object.wosize_of_object
             x_c39bed69b0e6a97dd42e9a16413dbcb1_1
             x_e246fc25c9201731c203dc9e18738560_0)))))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
        (forall ((@x1 Term))
         (! (implies
           (and
            (HasType @x1 Pulse.Spec.GC.Graph.edge_list)
            ;; def=Pulse.Spec.GC.GraphBridge.fst(31,10-57,5); use=Pulse.Spec.GC.GraphBridge.fst(36,2-57,5)
            (=
             @x1
             (let
               ((@lb2
                 (Prims.op_GreaterThanOrEqual
                  (FStar.UInt64.v x_fe73a94f2dd77d31df9370eb9a76c290_3)
                  (FStar.UInt64.v x_554e3198ce25a849d5e55a950b1f9de0_2))))
              (ite
               (= @lb2 (BoxBool true))
               (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)
               (let
                 ((@lb3
                   (Prims.op_AmpAmp
                    (Pulse.Spec.GC.Fields.is_pointer_field
                     (Pulse.Spec.GC.Heap.read_word
                      x_e246fc25c9201731c203dc9e18738560_0
                      (Pulse.Spec.GC.Fields.field_address
                       x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                       x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                    (Prims.op_disEquality
                     (FStar.UInt64.t Dummy_value)
                     (Pulse.Spec.GC.Heap.read_word
                      x_e246fc25c9201731c203dc9e18738560_0
                      (Pulse.Spec.GC.Fields.field_address
                       x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                       x_fe73a94f2dd77d31df9370eb9a76c290_3))
                     (FStar.UInt64.uint_to_t (BoxInt 0))))))
                (ite
                 (= @lb3 (BoxBool true))
                 (FStar.Seq.Base.cons
                  U_zero
                  Pulse.Spec.GC.Graph.edge
                  (FStar.Pervasives.Native.Mktuple2
                   U_zero
                   U_zero
                   Pulse.Spec.GC.Graph.vertex_id
                   Pulse.Spec.GC.Graph.vertex_id
                   x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                   (Pulse.Spec.GC.Heap.read_word
                    x_e246fc25c9201731c203dc9e18738560_0
                    (Pulse.Spec.GC.Fields.field_address
                     x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                     x_fe73a94f2dd77d31df9370eb9a76c290_3)))
                  (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                   x_e246fc25c9201731c203dc9e18738560_0
                   x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                   x_554e3198ce25a849d5e55a950b1f9de0_2
                   (FStar.UInt64.add
                    x_fe73a94f2dd77d31df9370eb9a76c290_3
                    (FStar.UInt64.uint_to_t (BoxInt 1)))))
                 (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                  x_e246fc25c9201731c203dc9e18738560_0
                  x_c39bed69b0e6a97dd42e9a16413dbcb1_1
                  x_554e3198ce25a849d5e55a950b1f9de0_2
                  (FStar.UInt64.add
                   x_fe73a94f2dd77d31df9370eb9a76c290_3
                   (FStar.UInt64.uint_to_t (BoxInt 1))))))))))
           ;; def=Prims.fst(364,2-364,58); use=Prims.fst(434,19-434,31)
           (forall ((@x2 Term))
            (! (implies
              (and
               (HasType @x2 Pulse.Spec.GC.Graph.edge_list)
               ;; def=Prims.fst(364,26-364,41); use=Prims.fst(434,19-434,31)
               (= @x2 @x1))
              ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
              (Valid
               ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
               (ApplyTT @x0 @x2)))
             :qid @query.27)))
          :qid @query.26))))
      :qid @query.24))))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_18")
(eval label_18)
(echo "label_17")
(eval label_17)
(echo "label_16")
(eval label_16)
(echo "label_15")
(eval label_15)
(echo "label_14")
(eval label_14)
(echo "label_13")
(eval label_13)
(echo "label_12")
(eval label_12)
(echo "label_11")
(eval label_11)
(echo "label_10")
(eval label_10)
(echo "label_9")
(eval label_9)
(echo "label_8")
(eval label_8)
(echo "label_7")
(eval label_7)
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.collect_edges_from_object, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(push) ;; push{2
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (g: Pulse.Spec.GC.Base.heap).
;   (* - Could not prove post-condition *)
;   forall (h: Pulse.Spec.GC.Base.hp_addr).
;     Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;     (forall (any_result: Type0).
;         Pulse.Spec.GC.Base.hp_addr == any_result ==>
;         0 < Pulse.Spec.GC.Base.heap_size /\ 0 % FStar.UInt64.v Pulse.Spec.GC.Base.mword == 0)
; Context: While encoding a query
; While typechecking the top-level declaration `let all_objects_well_formed`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      ;; def=Pulse.Spec.GC.GraphBridge.fst(61,2-61,75); use=Pulse.Spec.GC.GraphBridge.fst(61,2-61,75)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
         ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(61,23-61,75)
         (and
          ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(61,34-61,41)
          (or
           label_1
           ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(61,34-61,41)
           (Valid
            ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(61,34-61,41)
            (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
          ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(61,23-61,75)
          (forall ((@x2 Term))
           (! (implies
             (and
              (HasType @x2 (Tm_type U_zero))
              ;; def=FStar.Seq.Properties.fsti(77,10-77,11); use=Pulse.Spec.GC.GraphBridge.fst(61,23-61,75)
              (= Pulse.Spec.GC.Base.hp_addr @x2))
             ;; def=Pulse.Spec.GC.Base.fsti(44,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(61,42-61,45)
             (and
              ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(61,42-61,45)
              (or
               label_2
               ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(61,42-61,45)
               (<
                (BoxInt_proj_0 (BoxInt 0))
                (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value))))
              ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(61,42-61,45)
              (or
               label_3
               ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(61,42-61,45)
               (=
                (Prims.op_Modulus (BoxInt 0) (FStar.UInt64.v (Pulse.Spec.GC.Base.mword Dummy_value)))
                (BoxInt 0)))))
            :qid @query.2))))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.all_objects_well_formed, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun FStar.Seq.Base.index (Universe Term Term Term) Term)
(declare-fun FStar.Seq.Base.slice (Universe Term Term Term Term) Term)
(declare-fun FStar.Seq.Properties.count (Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun FStar.Seq.Properties.count.fuel_instrumented (Fuel Term Term Term) Term)
(declare-fun FStar.Seq.Properties.head (Universe Term Term) Term)
(declare-fun FStar.Seq.Properties.mem (Term Term Term) Term)
(declare-fun FStar.Seq.Properties.tail (Universe Term Term) Term)
(declare-fun Prims.op_GreaterThan (Term Term) Term)
(declare-fun Tm_refine_160fe7faad9a466b3cae8455bac5be60 (Universe Term Term) Term)
(declare-fun Tm_refine_1628fa8159c35bdaa68f121a383a6a00 (Universe Term Term) Term)
(declare-fun Tm_refine_1ba8fd8bb363097813064c67740b2de5 (Term Term Term) Term)
(declare-fun Tm_refine_2ba3c396db0f8da46e306c3240572295 (Universe Term Term Term) Term)
(declare-fun Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 (Term Term) Term)
(declare-fun Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 (Universe Term Term Term) Term)
(declare-fun Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 (Universe Term) Term)
(declare-fun Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 (Universe Term Term Term) Term)
(declare-fun Tm_refine_bfee24de0a02daebc80201253b983289 (Term Term) Term)
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(71,8-71,13); use=FStar.Seq.Properties.fsti(71,8-71,13)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.Seq.Properties.count @x0 @x1 @x2)
     (FStar.Seq.Properties.count.fuel_instrumented MaxFuel @x0 @x1 @x2))
    :pattern ((FStar.Seq.Properties.count @x0 @x1 @x2))
    :qid @fuel_correspondence_FStar.Seq.Properties.count.fuel_instrumented))
  :named @fuel_correspondence_FStar.Seq.Properties.count.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(71,8-71,13); use=FStar.Seq.Properties.fsti(71,8-71,13)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0) @x1 @x2 @x3)
     (FStar.Seq.Properties.count.fuel_instrumented ZFuel @x1 @x2 @x3))
    :pattern ((FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0) @x1 @x2 @x3))
    :qid @fuel_irrelevance_FStar.Seq.Properties.count.fuel_instrumented))
  :named @fuel_irrelevance_FStar.Seq.Properties.count.fuel_instrumented))
; Equation for FStar.Seq.Properties.head
;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(40,4-40,8); use=FStar.Seq.Properties.fsti(40,4-40,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (FStar.Seq.Properties.head @u0 @x1 @x2) (FStar.Seq.Base.index @u0 @x1 @x2 (BoxInt 0)))
    :pattern ((FStar.Seq.Properties.head @u0 @x1 @x2))
    :qid equation_FStar.Seq.Properties.head))
  :named equation_FStar.Seq.Properties.head))
; Equation for FStar.Seq.Properties.mem
;;; Fact-ids: Name FStar.Seq.Properties.mem; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(77,4-77,7); use=FStar.Seq.Properties.fsti(77,4-77,7)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.Seq.Properties.mem @x0 @x1 @x2)
     (Prims.op_GreaterThan (FStar.Seq.Properties.count @x0 @x1 @x2) (BoxInt 0)))
    :pattern ((FStar.Seq.Properties.mem @x0 @x1 @x2))
    :qid equation_FStar.Seq.Properties.mem))
  :named equation_FStar.Seq.Properties.mem))
; Equation for FStar.Seq.Properties.tail
;;; Fact-ids: Name FStar.Seq.Properties.tail; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(42,4-42,8); use=FStar.Seq.Properties.fsti(42,4-42,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.Seq.Properties.tail @u0 @x1 @x2)
     (FStar.Seq.Base.slice @u0 @x1 @x2 (BoxInt 1) (FStar.Seq.Base.length @u0 @x1 @x2)))
    :pattern ((FStar.Seq.Properties.tail @u0 @x1 @x2))
    :qid equation_FStar.Seq.Properties.tail))
  :named equation_FStar.Seq.Properties.tail))
; Equation for fuel-instrumented recursive function: FStar.Seq.Properties.count
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(71,8-71,13); use=FStar.Seq.Properties.fsti(71,8-71,13)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 Prims.eqtype) (HasType @x2 @x1) (HasType @x3 (FStar.Seq.Base.seq U_zero @x1)))
     (=
      (FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0) @x1 @x2 @x3)
      (let ((@lb4 (Prims.op_Equality Prims.int (FStar.Seq.Base.length U_zero @x1 @x3) (BoxInt 0))))
       (ite
        (= @lb4 (BoxBool true))
        (BoxInt 0)
        (let ((@lb5 (Prims.op_Equality @x1 (FStar.Seq.Properties.head U_zero @x1 @x3) @x2)))
         (ite
          (= @lb5 (BoxBool true))
          (Prims.op_Addition
           (BoxInt 1)
           (FStar.Seq.Properties.count.fuel_instrumented
            @u0
            @x1
            @x2
            (FStar.Seq.Properties.tail U_zero @x1 @x3)))
          (FStar.Seq.Properties.count.fuel_instrumented
           @u0
           @x1
           @x2
           (FStar.Seq.Properties.tail U_zero @x1 @x3))))))))
    :weight 0
    :pattern ((FStar.Seq.Properties.count.fuel_instrumented (SFuel @u0) @x1 @x2 @x3))
    :qid equation_with_fuel_FStar.Seq.Properties.count.fuel_instrumented))
  :named equation_with_fuel_FStar.Seq.Properties.count.fuel_instrumented))
; haseq for Tm_refine_160fe7faad9a466b3cae8455bac5be60
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2))))
    :qid haseqTm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named haseqTm_refine_160fe7faad9a466b3cae8455bac5be60))
; haseq for Tm_refine_1628fa8159c35bdaa68f121a383a6a00
;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(382,59-382,89); use=FStar.Seq.Properties.fsti(382,59-382,89)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u0 @x1 @x2))))
    :qid haseqTm_refine_1628fa8159c35bdaa68f121a383a6a00))
  :named haseqTm_refine_1628fa8159c35bdaa68f121a383a6a00))
; haseq for Tm_refine_1ba8fd8bb363097813064c67740b2de5
;;; Fact-ids: Name FStar.Seq.Properties.slice_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(625,2-625,40); use=FStar.Seq.Properties.fsti(625,2-625,40)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x0 @x1 @x2))))
    :qid haseqTm_refine_1ba8fd8bb363097813064c67740b2de5))
  :named haseqTm_refine_1ba8fd8bb363097813064c67740b2de5))
; haseq for Tm_refine_2ba3c396db0f8da46e306c3240572295
;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(276,53-276,82); use=FStar.Seq.Properties.fsti(276,53-276,82)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_2ba3c396db0f8da46e306c3240572295))
  :named haseqTm_refine_2ba3c396db0f8da46e306c3240572295))
; haseq for Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,88-158,104); use=FStar.Seq.Base.fsti(158,88-158,104)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x0 @x1)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x0 @x1))))
    :qid haseqTm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
  :named haseqTm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
; haseq for Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13
;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(64,43-64,73); use=FStar.Seq.Base.fsti(64,43-64,73)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
  :named haseqTm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
; haseq for Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1
;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(40,19-40,42); use=FStar.Seq.Properties.fsti(40,19-40,42)
  (forall ((@u0 Universe) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1)))
     (Valid (Prims.hasEq @u0 (FStar.Seq.Base.seq @u0 @x1))))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1))))
    :qid haseqTm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
  :named haseqTm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
; haseq for Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,54-158,84); use=FStar.Seq.Base.fsti(158,54-158,84)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
  :named haseqTm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
; haseq for Tm_refine_bfee24de0a02daebc80201253b983289
;;; Fact-ids: Name FStar.Seq.Properties.seq_mem_k; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(421,39-421,62); use=FStar.Seq.Properties.fsti(421,39-421,62)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_bfee24de0a02daebc80201253b983289 @x0 @x1)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_bfee24de0a02daebc80201253b983289 @x0 @x1))))
    :qid haseqTm_refine_bfee24de0a02daebc80201253b983289))
  :named haseqTm_refine_bfee24de0a02daebc80201253b983289))
; Lemma: FStar.Seq.Base.lemma_index_slice
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x3 @x1 @x2))
      (HasType @x5 (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x4 @x3)))
     ;; def=FStar.Seq.Base.fsti(160,11-160,53); use=FStar.Seq.Base.fsti(160,11-160,53)
     (=
      (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) @x5)
      (FStar.Seq.Base.index @u0 @x1 @x2 (Prims.op_Addition @x5 @x3))))
    :pattern ((FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) @x5))
    :qid lemma_FStar.Seq.Base.lemma_index_slice))
  :named lemma_FStar.Seq.Base.lemma_index_slice))
; Lemma: FStar.Seq.Base.lemma_len_slice
;;; Fact-ids: Name FStar.Seq.Base.lemma_len_slice; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x3 @x1 @x2)))
     ;; def=FStar.Seq.Base.fsti(129,11-129,41); use=FStar.Seq.Base.fsti(129,11-129,41)
     (=
      (FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4))
      (Prims.op_Subtraction @x4 @x3)))
    :pattern ((FStar.Seq.Base.length @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)))
    :qid lemma_FStar.Seq.Base.lemma_len_slice))
  :named lemma_FStar.Seq.Base.lemma_len_slice))
; Lemma: FStar.Seq.Properties.lemma_tail_slice
;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u0 @x3 @x1 @x2)))
     ;; def=FStar.Seq.Properties.fsti(279,11-279,52); use=FStar.Seq.Properties.fsti(279,11-279,52)
     (=
      (FStar.Seq.Properties.tail @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4))
      (FStar.Seq.Base.slice @u0 @x1 @x2 (Prims.op_Addition @x3 (BoxInt 1)) @x4)))
    :pattern ((FStar.Seq.Properties.tail @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)))
    :qid lemma_FStar.Seq.Properties.lemma_tail_slice))
  :named lemma_FStar.Seq.Properties.lemma_tail_slice))
; Lemma: FStar.Seq.Properties.seq_mem_k
;;; Fact-ids: Name FStar.Seq.Properties.seq_mem_k; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x0 Prims.eqtype)
      (HasType @x1 (FStar.Seq.Base.seq U_zero @x0))
      (HasType @x2 (Tm_refine_bfee24de0a02daebc80201253b983289 @x0 @x1)))
     ;; def=FStar.Seq.Properties.fsti(423,19-423,42); use=FStar.Seq.Properties.fsti(423,19-423,42)
     (BoxBool_proj_0 (FStar.Seq.Properties.mem @x0 (FStar.Seq.Base.index U_zero @x0 @x1 @x2) @x1)))
    :pattern ((FStar.Seq.Properties.mem @x0 (FStar.Seq.Base.index U_zero @x0 @x1 @x2) @x1))
    :qid lemma_FStar.Seq.Properties.seq_mem_k))
  :named lemma_FStar.Seq.Properties.seq_mem_k))
; Lemma: FStar.Seq.Properties.slice_is_empty
;;; Fact-ids: Name FStar.Seq.Properties.slice_is_empty; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u0 @x1 @x2)))
     ;; def=FStar.Seq.Properties.fsti(608,11-608,37); use=FStar.Seq.Properties.fsti(608,11-608,37)
     (= (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x3) (FStar.Seq.Base.empty @u0 @x1)))
    :pattern ((FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x3))
    :qid lemma_FStar.Seq.Properties.slice_is_empty))
  :named lemma_FStar.Seq.Properties.slice_is_empty))
; Lemma: FStar.Seq.Properties.slice_length
;;; Fact-ids: Name FStar.Seq.Properties.slice_length; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)))
     ;; def=FStar.Seq.Properties.fsti(616,11-616,38); use=FStar.Seq.Properties.fsti(616,11-616,38)
     (= (FStar.Seq.Base.slice @u0 @x1 @x2 (BoxInt 0) (FStar.Seq.Base.length @u0 @x1 @x2)) @x2))
    :pattern ((FStar.Seq.Base.slice @u0 @x1 @x2 (BoxInt 0) (FStar.Seq.Base.length @u0 @x1 @x2)))
    :qid lemma_FStar.Seq.Properties.slice_length))
  :named lemma_FStar.Seq.Properties.slice_length))
; Lemma: FStar.Seq.Properties.slice_slice
;;; Fact-ids: Name FStar.Seq.Properties.slice_slice; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x3 @x1 @x2))
      (HasType @x5 Prims.nat)
      (HasType @x6 (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x5 @x4 @x3)))
     ;; def=FStar.Seq.Properties.fsti(628,11-628,71); use=FStar.Seq.Properties.fsti(628,11-628,71)
     (=
      (FStar.Seq.Base.slice @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) @x5 @x6)
      (FStar.Seq.Base.slice @u0 @x1 @x2 (Prims.op_Addition @x3 @x5) (Prims.op_Addition @x3 @x6))))
    :pattern ((FStar.Seq.Base.slice @u0 @x1 (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) @x5 @x6))
    :qid lemma_FStar.Seq.Properties.slice_slice))
  :named lemma_FStar.Seq.Properties.slice_slice))
;;; Fact-ids: Name Prims.op_GreaterThan; Namespace Prims
(assert
 (! ;; def=Prims.fst(578,4-578,18); use=Prims.fst(578,4-578,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_GreaterThan @x0 @x1) (BoxBool (> (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThan @x0 @x1))
    :qid primitive_Prims.op_GreaterThan))
  :named primitive_Prims.op_GreaterThan))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=FStar.Seq.Base.fsti(32,40-32,52)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named refinement_interpretation_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(382,59-382,89); use=FStar.Seq.Properties.fsti(382,59-382,89)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(382,68-382,87); use=FStar.Seq.Properties.fsti(382,68-382,87)
      (<= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_1628fa8159c35bdaa68f121a383a6a00))
  :named refinement_interpretation_Tm_refine_1628fa8159c35bdaa68f121a383a6a00))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.slice_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(625,2-625,40); use=FStar.Seq.Properties.fsti(625,2-625,40)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(625,12-625,20); use=FStar.Seq.Properties.fsti(625,12-625,20)
      (<= (BoxInt_proj_0 @x2) (BoxInt_proj_0 @x1))
      ;; def=FStar.Seq.Properties.fsti(625,24-625,37); use=FStar.Seq.Properties.fsti(625,24-625,37)
      (<= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (Prims.op_Subtraction @x3 @x4)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_1ba8fd8bb363097813064c67740b2de5))
  :named refinement_interpretation_Tm_refine_1ba8fd8bb363097813064c67740b2de5))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(276,53-276,82); use=FStar.Seq.Properties.fsti(276,53-276,82)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      (BoxBool_proj_0 (Prims.op_LessThan @x3 @x1))
      (BoxBool_proj_0 (Prims.op_LessThanOrEqual @x1 (FStar.Seq.Base.length @u2 @x4 @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_2ba3c396db0f8da46e306c3240572295))
  :named refinement_interpretation_Tm_refine_2ba3c396db0f8da46e306c3240572295))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,88-158,104); use=FStar.Seq.Base.fsti(158,88-158,104)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(158,94-158,103); use=FStar.Seq.Base.fsti(158,94-158,103)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (Prims.op_Subtraction @x2 @x3)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
  :named refinement_interpretation_Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(64,43-64,73); use=FStar.Seq.Base.fsti(64,43-64,73)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      (BoxBool_proj_0 (Prims.op_LessThanOrEqual @x3 @x1))
      (BoxBool_proj_0 (Prims.op_LessThanOrEqual @x1 (FStar.Seq.Base.length @u2 @x4 @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
  :named refinement_interpretation_Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(40,19-40,42); use=FStar.Seq.Properties.fsti(40,19-40,42)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq @u2 @x3))
      ;; def=FStar.Seq.Properties.fsti(40,28-40,40); use=FStar.Seq.Properties.fsti(40,28-40,40)
      (> (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x1)) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u2 @x3)))
    :qid refinement_interpretation_Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
  :named refinement_interpretation_Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,54-158,84); use=FStar.Seq.Base.fsti(158,54-158,84)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(158,60-158,66); use=FStar.Seq.Base.fsti(158,60-158,66)
      (<= (BoxInt_proj_0 @x3) (BoxInt_proj_0 @x1))
      ;; def=FStar.Seq.Base.fsti(158,70-158,83); use=FStar.Seq.Base.fsti(158,70-158,83)
      (<= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x4 @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
  :named refinement_interpretation_Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.seq_mem_k; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(421,39-421,62); use=FStar.Seq.Properties.fsti(421,39-421,62)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_bfee24de0a02daebc80201253b983289 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(421,45-421,61); use=FStar.Seq.Properties.fsti(421,45-421,61)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length U_zero @x2 @x3)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_bfee24de0a02daebc80201253b983289 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_bfee24de0a02daebc80201253b983289))
  :named refinement_interpretation_Tm_refine_bfee24de0a02daebc80201253b983289))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,34-32,53); use=FStar.Seq.Base.fsti(32,34-32,53)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
  :named refinement_kinding_Tm_refine_160fe7faad9a466b3cae8455bac5be60))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.seq_find_aux; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(382,59-382,89); use=FStar.Seq.Properties.fsti(382,59-382,89)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_1628fa8159c35bdaa68f121a383a6a00 @u0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_1628fa8159c35bdaa68f121a383a6a00))
  :named refinement_kinding_Tm_refine_1628fa8159c35bdaa68f121a383a6a00))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.slice_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(625,2-625,40); use=FStar.Seq.Properties.fsti(625,2-625,40)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_1ba8fd8bb363097813064c67740b2de5 @x0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_1ba8fd8bb363097813064c67740b2de5))
  :named refinement_kinding_Tm_refine_1ba8fd8bb363097813064c67740b2de5))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.lemma_tail_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(276,53-276,82); use=FStar.Seq.Properties.fsti(276,53-276,82)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_2ba3c396db0f8da46e306c3240572295 @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2ba3c396db0f8da46e306c3240572295))
  :named refinement_kinding_Tm_refine_2ba3c396db0f8da46e306c3240572295))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,88-158,104); use=FStar.Seq.Base.fsti(158,88-158,104)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
  :named refinement_kinding_Tm_refine_35a0739c434508f48d0bb1d5cd5df9e8))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(64,43-64,73); use=FStar.Seq.Base.fsti(64,43-64,73)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
  :named refinement_kinding_Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(40,19-40,42); use=FStar.Seq.Properties.fsti(40,19-40,42)
  (forall ((@u0 Universe) (@x1 Term))
   (! (HasType (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
  :named refinement_kinding_Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(158,54-158,84); use=FStar.Seq.Base.fsti(158,54-158,84)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0 @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
  :named refinement_kinding_Tm_refine_b9ca4cf05147d86d6eff56ccafdd09d0))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.seq_mem_k; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(421,39-421,62); use=FStar.Seq.Properties.fsti(421,39-421,62)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_bfee24de0a02daebc80201253b983289 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_bfee24de0a02daebc80201253b983289 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_bfee24de0a02daebc80201253b983289))
  :named refinement_kinding_Tm_refine_bfee24de0a02daebc80201253b983289))
; Typing correspondence of token to term
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(71,8-71,13); use=FStar.Seq.Properties.fsti(71,8-71,13)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 Prims.eqtype) (HasType @x2 @x1) (HasType @x3 (FStar.Seq.Base.seq U_zero @x1)))
     (HasType (FStar.Seq.Properties.count.fuel_instrumented @u0 @x1 @x2 @x3) Prims.nat))
    :pattern ((FStar.Seq.Properties.count.fuel_instrumented @u0 @x1 @x2 @x3))
    :qid token_correspondence_FStar.Seq.Properties.count.fuel_instrumented))
  :named token_correspondence_FStar.Seq.Properties.count.fuel_instrumented))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.index; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(32,4-32,9); use=FStar.Seq.Base.fsti(32,4-32,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)))
     (HasType (FStar.Seq.Base.index @u0 @x1 @x2 @x3) @x1))
    :pattern ((FStar.Seq.Base.index @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Base.index))
  :named typing_FStar.Seq.Base.index))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.slice; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(64,4-64,9); use=FStar.Seq.Base.fsti(64,4-64,9)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_5a92b6e4e7af9363bc35e43d9d7f3f13 @u0 @x3 @x1 @x2)))
     (HasType (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4))
    :qid typing_FStar.Seq.Base.slice))
  :named typing_FStar.Seq.Base.slice))
; free var typing
;;; Fact-ids: Name FStar.Seq.Properties.count; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(71,8-71,13); use=FStar.Seq.Properties.fsti(71,8-71,13)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x0 Prims.eqtype) (HasType @x1 @x0) (HasType @x2 (FStar.Seq.Base.seq U_zero @x0)))
     (HasType (FStar.Seq.Properties.count @x0 @x1 @x2) Prims.nat))
    :pattern ((FStar.Seq.Properties.count @x0 @x1 @x2))
    :qid typing_FStar.Seq.Properties.count))
  :named typing_FStar.Seq.Properties.count))
; free var typing
;;; Fact-ids: Name FStar.Seq.Properties.head; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(40,4-40,8); use=FStar.Seq.Properties.fsti(40,4-40,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1)))
     (HasType (FStar.Seq.Properties.head @u0 @x1 @x2) @x1))
    :pattern ((FStar.Seq.Properties.head @u0 @x1 @x2))
    :qid typing_FStar.Seq.Properties.head))
  :named typing_FStar.Seq.Properties.head))
; free var typing
;;; Fact-ids: Name FStar.Seq.Properties.mem; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(77,4-77,7); use=FStar.Seq.Properties.fsti(77,4-77,7)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x0 Prims.eqtype) (HasType @x1 @x0) (HasType @x2 (FStar.Seq.Base.seq U_zero @x0)))
     (HasType (FStar.Seq.Properties.mem @x0 @x1 @x2) Prims.bool))
    :pattern ((FStar.Seq.Properties.mem @x0 @x1 @x2))
    :qid typing_FStar.Seq.Properties.mem))
  :named typing_FStar.Seq.Properties.mem))
; free var typing
;;; Fact-ids: Name FStar.Seq.Properties.tail; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(42,4-42,8); use=FStar.Seq.Properties.fsti(42,4-42,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1)))
     (HasType (FStar.Seq.Properties.tail @u0 @x1 @x2) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Properties.tail @u0 @x1 @x2))
    :qid typing_FStar.Seq.Properties.tail))
  :named typing_FStar.Seq.Properties.tail))
(push) ;; push{2
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (g: Pulse.Spec.GC.Base.heap) (objs: FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr).
;   (* - Could not prove post-condition *)
;   forall (h: Pulse.Spec.GC.Base.hp_addr).
;     Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;     (FStar.Seq.Properties.mem h objs ==>
;       Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;       (forall (any_result: Type0).
;           Pulse.Spec.GC.Base.hp_addr == any_result ==>
;           0 < Pulse.Spec.GC.Base.heap_size /\ 0 % FStar.UInt64.v Pulse.Spec.GC.Base.mword == 0))
; Context: While encoding a query
; While typechecking the top-level declaration `let objs_subset_of_objects`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and
       (HasType @x0 Pulse.Spec.GC.Base.heap)
       (HasType @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr)))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(65,2-65,67); use=Pulse.Spec.GC.GraphBridge.fst(65,2-65,67)
      (forall ((@x2 Term))
       (! (implies
         (HasType @x2 Pulse.Spec.GC.Base.hp_addr)
         ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,67)
         (and
          ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,33-65,37)
          (or
           label_1
           ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,33-65,37)
           (Valid
            ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,33-65,37)
            (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
          (implies
           ;; def=Pulse.Spec.GC.GraphBridge.fst(65,23-65,37); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,37)
           (BoxBool_proj_0 (FStar.Seq.Properties.mem Pulse.Spec.GC.Base.hp_addr @x2 @x1))
           ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,67)
           (and
            ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,53-65,60)
            (or
             label_2
             ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,53-65,60)
             (Valid
              ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(65,53-65,60)
              (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
            ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,67)
            (forall ((@x3 Term))
             (! (implies
               (and
                (HasType @x3 (Tm_type U_zero))
                ;; def=FStar.Seq.Properties.fsti(77,10-77,11); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,67)
                (= Pulse.Spec.GC.Base.hp_addr @x3))
               ;; def=Pulse.Spec.GC.Base.fsti(44,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(65,61-65,64)
               (and
                ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(65,61-65,64)
                (or
                 label_3
                 ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(65,61-65,64)
                 (<
                  (BoxInt_proj_0 (BoxInt 0))
                  (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(65,61-65,64)
                (or
                 label_4
                 ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(65,61-65,64)
                 (=
                  (Prims.op_Modulus
                   (BoxInt 0)
                   (FStar.UInt64.v (Pulse.Spec.GC.Base.mword Dummy_value)))
                  (BoxInt 0)))))
              :qid @query.2))))))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun FStar.List.Tot.Base.hd (Universe Term Term) Term)
(declare-fun FStar.List.Tot.Base.index (Universe Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.index.fuel_instrumented (Fuel Universe Term Term Term) Term)
(declare-fun FStar.List.Tot.Base.length (Universe Term Term) Term)
; Fuel-instrumented function name
(declare-fun FStar.List.Tot.Base.length.fuel_instrumented (Fuel Universe Term Term) Term)
(declare-fun FStar.List.Tot.Base.tail (Universe Term Term) Term)
(declare-fun FStar.List.Tot.Base.tl (Universe Term Term) Term)
(declare-fun FStar.Seq.Base.seq_to_list (Universe Term Term) Term)
(declare-fun FStar.Seq.Properties.snoc (Universe Term Term Term) Term)
; Constructor
(declare-fun Prims.Cons (Universe Term Term Term) Term)
; Projector
(declare-fun Prims.Cons_@0 (Term) Universe)
; Projector
(declare-fun Prims.Cons_@a (Term) Term)
; Projector
(declare-fun Prims.Cons_@hd (Term) Term)
; Projector
(declare-fun Prims.Cons_@tl (Term) Term)
; Constructor
(declare-fun Prims.Nil (Universe Term) Term)
; Projector
(declare-fun Prims.Nil_@0 (Term) Universe)
; Projector
(declare-fun Prims.Nil_@a (Term) Term)
; Constructor
(declare-fun Prims.Refl (Universe Term Term) Term)
; Constructor base
(declare-fun Prims.Refl@base (Universe) Term)
; Projector
(declare-fun Prims.Refl_@0 (Term) Universe)
(declare-fun Prims.eq2 (Universe Term Term Term) Term)
; Constructor
(declare-fun Prims.equals (Universe Term Term Term) Term)
; token
(declare-fun Prims.equals@tok (Universe) Term)
; Constructor
(declare-fun Prims.list (Universe Term) Term)
; token
(declare-fun Prims.list@tok (Universe) Term)
(declare-fun Prims.uu___is_Cons (Universe Term Term) Term)
(declare-fun Tm_refine_444061fd0bd0053c4f27fa233082c9ca (Universe Term Term Term) Term)
(declare-fun Tm_refine_97286b406018c8659cdb053df840f284 (Universe Term Term) Term)
(declare-fun Tm_refine_9a97b1e6b8592dc7d674835070a48bbc (Universe Term Term Term) Term)
(declare-fun Tm_refine_c1424615841f28cac7fc34e92b7ff33c (Term) Term)
(declare-fun Tm_refine_f360832bc8ab26c0c0b0547e2b675640 (Universe Term) Term)
(declare-fun Tm_refine_f3a1334d3b10190c1395939660b6a4d8 (Universe Term Term) Term)
; Discriminator definition
(define-fun is-Prims.Cons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 325)
  (=
   __@x0
   (Prims.Cons
    (Prims.Cons_@0 __@x0)
    (Prims.Cons_@a __@x0)
    (Prims.Cons_@hd __@x0)
    (Prims.Cons_@tl __@x0)))))
; Discriminator definition
(define-fun is-Prims.Nil ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 320) (= __@x0 (Prims.Nil (Prims.Nil_@0 __@x0) (Prims.Nil_@a __@x0)))))
; Discriminator definition
(define-fun is-Prims.Refl ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 141)
  (exists ((@x0 Term) (@x1 Term))
   (! (= __@x0 (Prims.Refl (Prims.Refl_@0 __@x0) @x0 @x1)) :qid is-Prims.Refl))))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.List.Tot.Base.index @u0 @x1 @x2 @x3)
     (FStar.List.Tot.Base.index.fuel_instrumented MaxFuel @u0 @x1 @x2 @x3))
    :pattern ((FStar.List.Tot.Base.index @u0 @x1 @x2 @x3))
    :qid @fuel_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))
  :named @fuel_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.List.Tot.Base.length @u0 @x1 @x2)
     (FStar.List.Tot.Base.length.fuel_instrumented MaxFuel @u0 @x1 @x2))
    :pattern ((FStar.List.Tot.Base.length @u0 @x1 @x2))
    :qid @fuel_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))
  :named @fuel_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4)
     (FStar.List.Tot.Base.index.fuel_instrumented ZFuel @u1 @x2 @x3 @x4))
    :pattern ((FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4))
    :qid @fuel_irrelevance_FStar.List.Tot.Base.index.fuel_instrumented))
  :named @fuel_irrelevance_FStar.List.Tot.Base.index.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0) @u1 @x2 @x3)
     (FStar.List.Tot.Base.length.fuel_instrumented ZFuel @u1 @x2 @x3))
    :pattern ((FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0) @u1 @x2 @x3))
    :qid @fuel_irrelevance_FStar.List.Tot.Base.length.fuel_instrumented))
  :named @fuel_irrelevance_FStar.List.Tot.Base.length.fuel_instrumented))
; pretyping
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u1 @x0 (Prims.equals @u2 @x3 @x4 @x5))
     (= (Term_constr_id (Prims.equals @u2 @x3 @x4 @x5)) (Term_constr_id (PreType @x0))))
    :pattern ((HasTypeFuel @u1 @x0 (Prims.equals @u2 @x3 @x4 @x5)))
    :qid Prims_pretyping_b6caf3433f0e1f74e18cc20e042395f8))
  :named Prims_pretyping_b6caf3433f0e1f74e18cc20e042395f8))
; pretyping
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@x0 Term) (@u1 Fuel) (@u2 Universe) (@x3 Term))
   (! (implies (HasTypeFuel @u1 @x0 (Prims.list @u2 @x3)) (= (Prims.list @u2 @x3) (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 (Prims.list @u2 @x3)))
    :qid Prims_pretyping_da5ad05a41b0a8d46bda8000c9315425))
  :named Prims_pretyping_da5ad05a41b0a8d46bda8000c9315425))
; Assumption: Prims.list__uu___haseq
;;; Fact-ids: Name Prims.list__uu___haseq; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (forall ((@x1 Term))
     (! (implies
       (and (HasType @x1 (Tm_type @u0)) (Valid (Prims.hasEq @u0 @x1)))
       (Valid (Prims.hasEq @u0 (Prims.list @u0 @x1))))
      :pattern ((Prims.hasEq @u0 (Prims.list @u0 @x1)))
      :qid assumption_Prims.list__uu___haseq.1))
    :qid assumption_Prims.list__uu___haseq))
  :named assumption_Prims.list__uu___haseq))
; Constructor base
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (is-Prims.Refl (Prims.Refl @u0 @x1 @x2))
     (= (Prims.Refl @u0 @x1 @x2) (Prims.Refl@base @u0)))
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid constructor_base_Prims.Refl))
  :named constructor_base_Prims.Refl))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= 325 (Term_constr_id (Prims.Cons @u0 @x1 @x2 @x3)))
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid constructor_distinct_Prims.Cons))
  :named constructor_distinct_Prims.Cons))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 320 (Term_constr_id (Prims.Nil @u0 @x1)))
    :pattern ((Prims.Nil @u0 @x1))
    :qid constructor_distinct_Prims.Nil))
  :named constructor_distinct_Prims.Nil))
; Constructor distinct
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= 141 (Term_constr_id (Prims.Refl @u0 @x1 @x2)))
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid constructor_distinct_Prims.Refl))
  :named constructor_distinct_Prims.Refl))
; Constructor distinct
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= 134 (Term_constr_id (Prims.equals @u0 @x1 @x2 @x3)))
    :pattern ((Prims.equals @u0 @x1 @x2 @x3))
    :qid constructor_distinct_Prims.equals))
  :named constructor_distinct_Prims.equals))
; Constructor distinct
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= 313 (Term_constr_id (Prims.list @u0 @x1)))
    :pattern ((Prims.list @u0 @x1))
    :qid constructor_distinct_Prims.list))
  :named constructor_distinct_Prims.list))
; data constructor typing elim
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5))
     (and
      (HasTypeFuel @u0 @x5 (Tm_type @u1))
      (HasTypeFuel @u0 @x3 @x5)
      (HasTypeFuel @u0 @x4 (Prims.list @u1 @x5))))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5)))
    :qid data_elim_Prims.Cons))
  :named data_elim_Prims.Cons))
; data constructor typing elim
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Nil @u1 @x2) (Prims.list @u1 @x3))
     (HasTypeFuel @u0 @x3 (Tm_type @u1)))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Nil @u1 @x2) (Prims.list @u1 @x3)))
    :qid data_elim_Prims.Nil))
  :named data_elim_Prims.Nil))
; data constructor typing elim
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x4 @x5 @x6))
     (and (= @x5 @x6) (HasTypeFuel @u0 @x4 (Tm_type @u1)) (HasTypeFuel @u0 @x5 @x4)))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x4 @x5 @x6)))
    :qid data_elim_Prims.Refl))
  :named data_elim_Prims.Refl))
; data constructor typing intro
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x2 (Tm_type @u1))
      (HasTypeFuel @u0 @x3 @x2)
      (HasTypeFuel @u0 @x4 (Prims.list @u1 @x2)))
     (HasTypeFuel @u0 (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x2)))
    :pattern ((HasTypeFuel @u0 (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x2)))
    :qid data_typing_intro_Prims.Cons@tok))
  :named data_typing_intro_Prims.Cons@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term))
   (! (implies
     (HasTypeFuel @u0 @x2 (Tm_type @u1))
     (HasTypeFuel @u0 (Prims.Nil @u1 @x2) (Prims.list @u1 @x2)))
    :pattern ((HasTypeFuel @u0 (Prims.Nil @u1 @x2) (Prims.list @u1 @x2)))
    :qid data_typing_intro_Prims.Nil@tok))
  :named data_typing_intro_Prims.Nil@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and (HasTypeFuel @u0 @x2 (Tm_type @u1)) (HasTypeFuel @u0 @x3 @x2) (= @x3 @x4))
     (HasTypeFuel @u0 (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x2 @x3 @x4)))
    :pattern ((HasTypeFuel @u0 (Prims.Refl @u1 @x2 @x3) (Prims.equals @u1 @x2 @x3 @x4)))
    :qid data_typing_intro_Prims.Refl@tok))
  :named data_typing_intro_Prims.Refl@tok))
; Discriminator equation
;;; Fact-ids: Name Prims.uu___is_Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.uu___is_Cons @u0 @x1 @x2) (BoxBool (is-Prims.Cons @x2)))
    :pattern ((Prims.uu___is_Cons @u0 @x1 @x2))
    :qid disc_equation_Prims.Cons))
  :named disc_equation_Prims.Cons))
; Eq2 interpretation
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff (= @x2 @x3) (Valid (Prims.eq2 @u0 @x1 @x2 @x3)))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid eq2-interp))
  :named eq2-interp))
; Equation for FStar.List.Tot.Base.hd
;;; Fact-ids: Name FStar.List.Tot.Base.hd; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(39,4-39,6); use=FStar.List.Tot.Base.fst(39,4-39,6)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.List.Tot.Base.hd @u0 @x1 @x2)
     (let ((@lb3 @x2)) (ite (is-Prims.Cons @lb3) (Prims.Cons_@hd @lb3) Tm_unit)))
    :pattern ((FStar.List.Tot.Base.hd @u0 @x1 @x2))
    :qid equation_FStar.List.Tot.Base.hd))
  :named equation_FStar.List.Tot.Base.hd))
; Equation for FStar.List.Tot.Base.tail
;;; Fact-ids: Name FStar.List.Tot.Base.tail; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(46,4-46,8); use=FStar.List.Tot.Base.fst(46,4-46,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.List.Tot.Base.tail @u0 @x1 @x2)
     (let ((@lb3 @x2)) (ite (is-Prims.Cons @lb3) (Prims.Cons_@tl @lb3) Tm_unit)))
    :pattern ((FStar.List.Tot.Base.tail @u0 @x1 @x2))
    :qid equation_FStar.List.Tot.Base.tail))
  :named equation_FStar.List.Tot.Base.tail))
; Equation for FStar.List.Tot.Base.tl
;;; Fact-ids: Name FStar.List.Tot.Base.tl; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(53,4-53,6); use=FStar.List.Tot.Base.fst(53,4-53,6)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (FStar.List.Tot.Base.tl @u0 @x1 @x2) (FStar.List.Tot.Base.tail @u0 @x1 @x2))
    :pattern ((FStar.List.Tot.Base.tl @u0 @x1 @x2))
    :qid equation_FStar.List.Tot.Base.tl))
  :named equation_FStar.List.Tot.Base.tl))
; Equation for FStar.Seq.Properties.snoc
;;; Fact-ids: Name FStar.Seq.Properties.snoc; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(316,4-316,8); use=FStar.Seq.Properties.fsti(316,4-316,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (FStar.Seq.Properties.snoc @u0 @x1 @x2 @x3)
     (FStar.Seq.Base.append @u0 @x1 @x2 (FStar.Seq.Base.create @u0 @x1 (BoxInt 1) @x3)))
    :pattern ((FStar.Seq.Properties.snoc @u0 @x1 @x2 @x3))
    :qid equation_FStar.Seq.Properties.snoc))
  :named equation_FStar.Seq.Properties.snoc))
; Equation for Prims.eq2
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! ;; def=Prims.fst(183,5-183,8); use=Prims.fst(183,5-183,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.eq2 @u0 @x1 @x2 @x3) (Prims.squash U_zero (Prims.equals @u0 @x1 @x2 @x3)))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid equation_Prims.eq2))
  :named equation_Prims.eq2))
; Equation for fuel-instrumented recursive function: FStar.List.Tot.Base.index
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x2 (Tm_type @u1))
      (HasType @x3 (Prims.list @u1 @x2))
      (HasType @x4 (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u1 @x2 @x3)))
     (=
      (FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4)
      (let ((@lb5 (Prims.op_Equality Prims.int @x4 (BoxInt 0))))
       (ite
        (= @lb5 (BoxBool true))
        (FStar.List.Tot.Base.hd @u1 @x2 @x3)
        (FStar.List.Tot.Base.index.fuel_instrumented
         @u0
         @u1
         @x2
         (FStar.List.Tot.Base.tl @u1 @x2 @x3)
         (Prims.op_Subtraction @x4 (BoxInt 1)))))))
    :weight 0
    :pattern ((FStar.List.Tot.Base.index.fuel_instrumented (SFuel @u0) @u1 @x2 @x3 @x4))
    :qid equation_with_fuel_FStar.List.Tot.Base.index.fuel_instrumented))
  :named equation_with_fuel_FStar.List.Tot.Base.index.fuel_instrumented))
; Equation for fuel-instrumented recursive function: FStar.List.Tot.Base.length
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u1)) (HasType @x3 (Prims.list @u1 @x2)))
     (=
      (FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0) @u1 @x2 @x3)
      (let ((@lb4 @x3))
       (ite
        (is-Prims.Nil @lb4)
        (BoxInt 0)
        (ite
         (is-Prims.Cons @lb4)
         (Prims.op_Addition
          (BoxInt 1)
          (FStar.List.Tot.Base.length.fuel_instrumented @u0 @u1 @x2 (Prims.Cons_@tl @lb4)))
         Tm_unit)))))
    :weight 0
    :pattern ((FStar.List.Tot.Base.length.fuel_instrumented (SFuel @u0) @u1 @x2 @x3))
    :qid equation_with_fuel_FStar.List.Tot.Base.length.fuel_instrumented))
  :named equation_with_fuel_FStar.List.Tot.Base.length.fuel_instrumented))
; fresh token
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (= 135 (Term_constr_id (Prims.equals@tok @u0)))
    :pattern ((Prims.equals@tok @u0))
    :qid fresh_token_Prims.equals@tok))
  :named fresh_token_Prims.equals@tok))
; fresh token
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! (forall ((@u0 Universe))
   (! (= 314 (Term_constr_id (Prims.list@tok @u0)))
    :pattern ((Prims.list@tok @u0))
    :qid fresh_token_Prims.list@tok))
  :named fresh_token_Prims.list@tok))
; inversion axiom
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Prims.equals @u2 @x3 @x4 @x5))
     (and (is-Prims.Refl @x1) (= @u2 (Prims.Refl_@0 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Prims.equals @u2 @x3 @x4 @x5)))
    :qid fuel_guarded_inversion_Prims.equals))
  :named fuel_guarded_inversion_Prims.equals))
; inversion axiom
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) @x1 (Prims.list @u2 @x3))
     (or
      (and (is-Prims.Nil @x1) (= @u2 (Prims.Nil_@0 @x1)) (= @x3 (Prims.Nil_@a @x1)))
      (and (is-Prims.Cons @x1) (= @u2 (Prims.Cons_@0 @x1)) (= @x3 (Prims.Cons_@a @x1)))))
    :pattern ((HasTypeFuel (SFuel @u0) @x1 (Prims.list @u2 @x3)))
    :qid fuel_guarded_inversion_Prims.list))
  :named fuel_guarded_inversion_Prims.list))
; haseq for Tm_refine_444061fd0bd0053c4f27fa233082c9ca
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_app2; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(153,57-153,107); use=FStar.Seq.Base.fsti(153,57-153,107)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_444061fd0bd0053c4f27fa233082c9ca))
  :named haseqTm_refine_444061fd0bd0053c4f27fa233082c9ca))
; haseq for Tm_refine_97286b406018c8659cdb053df840f284
;;; Fact-ids: Name FStar.Seq.Base.seq_to_list; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(28,42-28,79); use=FStar.Seq.Base.fsti(28,42-28,79)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_97286b406018c8659cdb053df840f284 @u0 @x1 @x2)))
     (Valid (Prims.hasEq @u0 (Prims.list @u0 @x1))))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_97286b406018c8659cdb053df840f284 @u0 @x1 @x2))))
    :qid haseqTm_refine_97286b406018c8659cdb053df840f284))
  :named haseqTm_refine_97286b406018c8659cdb053df840f284))
; haseq for Tm_refine_9a97b1e6b8592dc7d674835070a48bbc
;;; Fact-ids: Name FStar.Seq.Properties.snoc_slice_index; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(585,2-585,36); use=FStar.Seq.Properties.fsti(585,2-585,36)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_9a97b1e6b8592dc7d674835070a48bbc))
  :named haseqTm_refine_9a97b1e6b8592dc7d674835070a48bbc))
; haseq for Tm_refine_c1424615841f28cac7fc34e92b7ff33c
;;; Fact-ids: Name FStar.Seq.Base.init_aux; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(36,41-36,57); use=FStar.Seq.Base.fsti(36,41-36,57)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x0)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x0))))
    :qid haseqTm_refine_c1424615841f28cac7fc34e92b7ff33c))
  :named haseqTm_refine_c1424615841f28cac7fc34e92b7ff33c))
; haseq for Tm_refine_f360832bc8ab26c0c0b0547e2b675640
;;; Fact-ids: Name Prims.__proj__Cons__item__hd; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq @u0 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1)))
     (Valid (Prims.hasEq @u0 (Prims.list @u0 @x1))))
    :pattern ((Valid (Prims.hasEq @u0 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1))))
    :qid haseqTm_refine_f360832bc8ab26c0c0b0547e2b675640))
  :named haseqTm_refine_f360832bc8ab26c0c0b0547e2b675640))
; haseq for Tm_refine_f3a1334d3b10190c1395939660b6a4d8
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,29-90,50); use=FStar.List.Tot.Base.fst(90,29-90,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u0 @x1 @x2)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u0 @x1 @x2))))
    :qid haseqTm_refine_f3a1334d3b10190c1395939660b6a4d8))
  :named haseqTm_refine_f3a1334d3b10190c1395939660b6a4d8))
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! (and
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe))
    (! (IsTotFun (Prims.equals@tok @u0))
     :pattern ((Prims.equals@tok @u0))
     :qid kinding_Prims.equals@tok))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term))
    (! (IsTotFun (ApplyTT (Prims.equals@tok @u0) @x1))
     :pattern ((ApplyTT (Prims.equals@tok @u0) @x1))
     :qid kinding_Prims.equals@tok.1))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
    (! (IsTotFun (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2))
     :pattern ((ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2))
     :qid kinding_Prims.equals@tok.2))
   ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
   (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
    (! (implies
      (and (HasType @x1 (Tm_type @u0)) (HasType @x2 @x1) (HasType @x3 @x1))
      (HasType (Prims.equals @u0 @x1 @x2 @x3) (Tm_type U_zero)))
     :pattern ((Prims.equals @u0 @x1 @x2 @x3))
     :qid kinding_Prims.equals@tok.3)))
  :named kinding_Prims.equals@tok))
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! (and
   ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
   (forall ((@u0 Universe))
    (! (IsTotFun (Prims.list@tok @u0)) :pattern ((Prims.list@tok @u0)) :qid kinding_Prims.list@tok))
   ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
   (forall ((@u0 Universe) (@x1 Term))
    (! (implies (HasType @x1 (Tm_type @u0)) (HasType (Prims.list @u0 @x1) (Tm_type @u0)))
     :pattern ((Prims.list @u0 @x1))
     :qid kinding_Prims.list@tok.1)))
  :named kinding_Prims.list@tok))
; Lemma: FStar.Seq.Base.lemma_index_app1
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_app1; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x4 (Tm_refine_160fe7faad9a466b3cae8455bac5be60 @u0 @x1 @x2)))
     ;; def=FStar.Seq.Base.fsti(150,11-150,49); use=FStar.Seq.Base.fsti(150,11-150,49)
     (=
      (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3) @x4)
      (FStar.Seq.Base.index @u0 @x1 @x2 @x4)))
    :pattern ((FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3) @x4))
    :qid lemma_FStar.Seq.Base.lemma_index_app1))
  :named lemma_FStar.Seq.Base.lemma_index_app1))
; Lemma: FStar.Seq.Base.lemma_index_app2
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_app2; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x4 (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u0 @x1 @x2 @x3)))
     ;; def=FStar.Seq.Base.fsti(155,11-155,63); use=FStar.Seq.Base.fsti(155,11-155,63)
     (=
      (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3) @x4)
      (FStar.Seq.Base.index
       @u0
       @x1
       @x3
       (Prims.op_Subtraction @x4 (FStar.Seq.Base.length @u0 @x1 @x2)))))
    :pattern ((FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.append @u0 @x1 @x2 @x3) @x4))
    :qid lemma_FStar.Seq.Base.lemma_index_app2))
  :named lemma_FStar.Seq.Base.lemma_index_app2))
; Lemma: FStar.Seq.Base.lemma_index_create
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_create; Namespace FStar.Seq.Base
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 Prims.nat)
      (HasType @x3 @x1)
      (HasType @x4 (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x2)))
     ;; def=FStar.Seq.Base.fsti(135,11-135,38); use=FStar.Seq.Base.fsti(135,11-135,38)
     (= (FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.create @u0 @x1 @x2 @x3) @x4) @x3))
    :pattern ((FStar.Seq.Base.index @u0 @x1 (FStar.Seq.Base.create @u0 @x1 @x2 @x3) @x4))
    :qid lemma_FStar.Seq.Base.lemma_index_create))
  :named lemma_FStar.Seq.Base.lemma_index_create))
; Lemma: FStar.Seq.Properties.snoc_slice_index
;;; Fact-ids: Name FStar.Seq.Properties.snoc_slice_index; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u0 @x3 @x1 @x2)))
     ;; def=FStar.Seq.Properties.fsti(588,11-588,64); use=FStar.Seq.Properties.fsti(588,11-588,64)
     (=
      (FStar.Seq.Properties.snoc
       @u0
       @x1
       (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)
       (FStar.Seq.Base.index @u0 @x1 @x2 @x4))
      (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 (Prims.op_Addition @x4 (BoxInt 1)))))
    :pattern
     ((FStar.Seq.Properties.snoc
       @u0
       @x1
       (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)
       (FStar.Seq.Base.index @u0 @x1 @x2 @x4)))
    :qid lemma_FStar.Seq.Properties.snoc_slice_index))
  :named lemma_FStar.Seq.Properties.snoc_slice_index))
; kinding
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe))
   (! (is-Tm_arrow (PreType (Prims.equals@tok @u0)))
    :pattern ((Prims.equals@tok @u0))
    :qid pre_kinding_Prims.equals@tok))
  :named pre_kinding_Prims.equals@tok))
; kinding
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe))
   (! (is-Tm_arrow (PreType (Prims.list@tok @u0)))
    :pattern ((Prims.list@tok @u0))
    :qid pre_kinding_Prims.list@tok))
  :named pre_kinding_Prims.list@tok))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@0 (Prims.Cons @u0 @x1 @x2 @x3)) @u0)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@0))
  :named projection_inverse_Prims.Cons_@0))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@a (Prims.Cons @u0 @x1 @x2 @x3)) @x1)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@a))
  :named projection_inverse_Prims.Cons_@a))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@hd (Prims.Cons @u0 @x1 @x2 @x3)) @x2)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@hd))
  :named projection_inverse_Prims.Cons_@hd))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= (Prims.Cons_@tl (Prims.Cons @u0 @x1 @x2 @x3)) @x3)
    :pattern ((Prims.Cons @u0 @x1 @x2 @x3))
    :qid projection_inverse_Prims.Cons_@tl))
  :named projection_inverse_Prims.Cons_@tl))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.Nil_@0 (Prims.Nil @u0 @x1)) @u0)
    :pattern ((Prims.Nil @u0 @x1))
    :qid projection_inverse_Prims.Nil_@0))
  :named projection_inverse_Prims.Nil_@0))
; Projection inverse
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(617,4-617,7); use=Prims.fst(617,4-617,7)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (Prims.Nil_@a (Prims.Nil @u0 @x1)) @x1)
    :pattern ((Prims.Nil @u0 @x1))
    :qid projection_inverse_Prims.Nil_@a))
  :named projection_inverse_Prims.Nil_@a))
; Projection inverse
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,46-173,50); use=Prims.fst(173,46-173,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (= (Prims.Refl_@0 (Prims.Refl @u0 @x1 @x2)) @u0)
    :pattern ((Prims.Refl @u0 @x1 @x2))
    :qid projection_inverse_Prims.Refl_@0))
  :named projection_inverse_Prims.Refl_@0))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_app2; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(153,57-153,107); use=FStar.Seq.Base.fsti(153,57-153,107)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(153,63-153,88); use=FStar.Seq.Base.fsti(153,63-153,88)
      (<
       (BoxInt_proj_0 @x1)
       (BoxInt_proj_0
        (Prims.op_Addition (FStar.Seq.Base.length @u2 @x3 @x4) (FStar.Seq.Base.length @u2 @x3 @x5))))
      ;; def=FStar.Seq.Base.fsti(153,92-153,106); use=FStar.Seq.Base.fsti(153,92-153,106)
      (<= (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x3 @x4)) (BoxInt_proj_0 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_444061fd0bd0053c4f27fa233082c9ca))
  :named refinement_interpretation_Tm_refine_444061fd0bd0053c4f27fa233082c9ca))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.seq_to_list; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(28,42-28,79); use=FStar.Seq.Base.fsti(28,42-28,79)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_97286b406018c8659cdb053df840f284 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 (Prims.list @u2 @x3))
      ;; def=FStar.Seq.Base.fsti(28,52-28,77); use=FStar.Seq.Base.fsti(28,52-28,77)
      (= (FStar.List.Tot.Base.length @u2 @x3 @x1) (FStar.Seq.Base.length @u2 @x3 @x4))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_97286b406018c8659cdb053df840f284 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_97286b406018c8659cdb053df840f284))
  :named refinement_interpretation_Tm_refine_97286b406018c8659cdb053df840f284))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.snoc_slice_index; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(585,2-585,36); use=FStar.Seq.Properties.fsti(585,2-585,36)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(585,11-585,17); use=FStar.Seq.Properties.fsti(585,11-585,17)
      (<= (BoxInt_proj_0 @x3) (BoxInt_proj_0 @x1))
      ;; def=FStar.Seq.Properties.fsti(585,21-585,33); use=FStar.Seq.Properties.fsti(585,21-585,33)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x4 @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_9a97b1e6b8592dc7d674835070a48bbc))
  :named refinement_interpretation_Tm_refine_9a97b1e6b8592dc7d674835070a48bbc))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Base.init_aux; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(36,41-36,57); use=FStar.Seq.Base.fsti(36,41-36,57)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Base.fsti(36,48-36,55); use=FStar.Seq.Base.fsti(36,48-36,55)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 @x2))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x2)))
    :qid refinement_interpretation_Tm_refine_c1424615841f28cac7fc34e92b7ff33c))
  :named refinement_interpretation_Tm_refine_c1424615841f28cac7fc34e92b7ff33c))
; refinement_interpretation
;;; Fact-ids: Name Prims.__proj__Cons__item__hd; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (Prims.list @u2 @x3))
      ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
      (BoxBool_proj_0 (Prims.uu___is_Cons @u2 @x3 @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u2 @x3)))
    :qid refinement_interpretation_Tm_refine_f360832bc8ab26c0c0b0547e2b675640))
  :named refinement_interpretation_Tm_refine_f360832bc8ab26c0c0b0547e2b675640))
; refinement_interpretation
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,29-90,50); use=FStar.List.Tot.Base.fst(90,29-90,50)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u2 @x3 @x4))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.List.Tot.Base.fst(90,36-90,48); use=FStar.List.Tot.Base.fst(90,36-90,48)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.List.Tot.Base.length @u2 @x3 @x4)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u2 @x3 @x4)))
    :qid refinement_interpretation_Tm_refine_f3a1334d3b10190c1395939660b6a4d8))
  :named refinement_interpretation_Tm_refine_f3a1334d3b10190c1395939660b6a4d8))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.lemma_index_app2; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(153,57-153,107); use=FStar.Seq.Base.fsti(153,57-153,107)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_444061fd0bd0053c4f27fa233082c9ca @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_444061fd0bd0053c4f27fa233082c9ca))
  :named refinement_kinding_Tm_refine_444061fd0bd0053c4f27fa233082c9ca))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.seq_to_list; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(28,42-28,79); use=FStar.Seq.Base.fsti(28,42-28,79)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_97286b406018c8659cdb053df840f284 @u0 @x1 @x2) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_97286b406018c8659cdb053df840f284 @u0 @x1 @x2) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_97286b406018c8659cdb053df840f284))
  :named refinement_kinding_Tm_refine_97286b406018c8659cdb053df840f284))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.snoc_slice_index; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(585,2-585,36); use=FStar.Seq.Properties.fsti(585,2-585,36)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_9a97b1e6b8592dc7d674835070a48bbc @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_9a97b1e6b8592dc7d674835070a48bbc))
  :named refinement_kinding_Tm_refine_9a97b1e6b8592dc7d674835070a48bbc))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Base.init_aux; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(36,41-36,57); use=FStar.Seq.Base.fsti(36,41-36,57)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_c1424615841f28cac7fc34e92b7ff33c @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_c1424615841f28cac7fc34e92b7ff33c))
  :named refinement_kinding_Tm_refine_c1424615841f28cac7fc34e92b7ff33c))
; refinement kinding
;;; Fact-ids: Name Prims.__proj__Cons__item__hd; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term))
   (! (HasType (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1) (Tm_type @u0))
    :pattern ((HasType (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1) (Tm_type @u0)))
    :qid refinement_kinding_Tm_refine_f360832bc8ab26c0c0b0547e2b675640))
  :named refinement_kinding_Tm_refine_f360832bc8ab26c0c0b0547e2b675640))
; refinement kinding
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,29-90,50); use=FStar.List.Tot.Base.fst(90,29-90,50)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (HasType (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u0 @x1 @x2) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u0 @x1 @x2) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_f3a1334d3b10190c1395939660b6a4d8))
  :named refinement_kinding_Tm_refine_f3a1334d3b10190c1395939660b6a4d8))
; subterm ordering
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5))
     (and
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x3 (Prims.Cons @u1 @x2 @x3 @x4)))
      (Valid (Prims.precedes U_zero U_zero Prims.lex_t Prims.lex_t @x4 (Prims.Cons @u1 @x2 @x3 @x4)))))
    :pattern ((HasTypeFuel (SFuel @u0) (Prims.Cons @u1 @x2 @x3 @x4) (Prims.list @u1 @x5)))
    :qid subterm_ordering_Prims.Cons))
  :named subterm_ordering_Prims.Cons))
; Typing correspondence of token to term
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x2 (Tm_type @u1))
      (HasType @x3 (Prims.list @u1 @x2))
      (HasType @x4 (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u1 @x2 @x3)))
     (HasType (FStar.List.Tot.Base.index.fuel_instrumented @u0 @u1 @x2 @x3 @x4) @x2))
    :pattern ((FStar.List.Tot.Base.index.fuel_instrumented @u0 @u1 @x2 @x3 @x4))
    :qid token_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))
  :named token_correspondence_FStar.List.Tot.Base.index.fuel_instrumented))
; Typing correspondence of token to term
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
  (forall ((@u0 Fuel) (@u1 Universe) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x2 (Tm_type @u1)) (HasType @x3 (Prims.list @u1 @x2)))
     (HasType (FStar.List.Tot.Base.length.fuel_instrumented @u0 @u1 @x2 @x3) Prims.nat))
    :pattern ((FStar.List.Tot.Base.length.fuel_instrumented @u0 @u1 @x2 @x3))
    :qid token_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))
  :named token_correspondence_FStar.List.Tot.Base.length.fuel_instrumented))
; name-token correspondence
;;; Fact-ids: Name Prims.equals; Namespace Prims; Name Prims.Refl; Namespace Prims
(assert
 (! ;; def=Prims.fst(173,5-173,11); use=Prims.fst(173,5-173,11)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (ApplyTT (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2) @x3)
     (Prims.equals @u0 @x1 @x2 @x3))
    :pattern ((ApplyTT (ApplyTT (ApplyTT (Prims.equals@tok @u0) @x1) @x2) @x3))
    :pattern ((Prims.equals @u0 @x1 @x2 @x3))
    :qid token_correspondence_Prims.equals@tok))
  :named token_correspondence_Prims.equals@tok))
; name-token correspondence
;;; Fact-ids: Name Prims.list; Namespace Prims; Name Prims.Nil; Namespace Prims; Name Prims.Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(616,5-616,9); use=Prims.fst(616,5-616,9)
  (forall ((@u0 Universe) (@x1 Term))
   (! (= (ApplyTT (Prims.list@tok @u0) @x1) (Prims.list @u0 @x1))
    :pattern ((ApplyTT (Prims.list@tok @u0) @x1))
    :pattern ((Prims.list @u0 @x1))
    :qid token_correspondence_Prims.list@tok))
  :named token_correspondence_Prims.list@tok))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.hd; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(39,4-39,6); use=FStar.List.Tot.Base.fst(39,4-39,6)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1)))
     (HasType (FStar.List.Tot.Base.hd @u0 @x1 @x2) @x1))
    :pattern ((FStar.List.Tot.Base.hd @u0 @x1 @x2))
    :qid typing_FStar.List.Tot.Base.hd))
  :named typing_FStar.List.Tot.Base.hd))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.index; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(90,8-90,13); use=FStar.List.Tot.Base.fst(90,8-90,13)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Prims.list @u0 @x1))
      (HasType @x3 (Tm_refine_f3a1334d3b10190c1395939660b6a4d8 @u0 @x1 @x2)))
     (HasType (FStar.List.Tot.Base.index @u0 @x1 @x2 @x3) @x1))
    :pattern ((FStar.List.Tot.Base.index @u0 @x1 @x2 @x3))
    :qid typing_FStar.List.Tot.Base.index))
  :named typing_FStar.List.Tot.Base.index))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.length; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(74,8-74,14); use=FStar.List.Tot.Base.fst(74,8-74,14)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.list @u0 @x1)))
     (HasType (FStar.List.Tot.Base.length @u0 @x1 @x2) Prims.nat))
    :pattern ((FStar.List.Tot.Base.length @u0 @x1 @x2))
    :qid typing_FStar.List.Tot.Base.length))
  :named typing_FStar.List.Tot.Base.length))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.tail; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(46,4-46,8); use=FStar.List.Tot.Base.fst(46,4-46,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1)))
     (HasType (FStar.List.Tot.Base.tail @u0 @x1 @x2) (Prims.list @u0 @x1)))
    :pattern ((FStar.List.Tot.Base.tail @u0 @x1 @x2))
    :qid typing_FStar.List.Tot.Base.tail))
  :named typing_FStar.List.Tot.Base.tail))
; free var typing
;;; Fact-ids: Name FStar.List.Tot.Base.tl; Namespace FStar.List.Tot.Base
(assert
 (! ;; def=FStar.List.Tot.Base.fst(53,4-53,6); use=FStar.List.Tot.Base.fst(53,4-53,6)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_f360832bc8ab26c0c0b0547e2b675640 @u0 @x1)))
     (HasType (FStar.List.Tot.Base.tl @u0 @x1 @x2) (Prims.list @u0 @x1)))
    :pattern ((FStar.List.Tot.Base.tl @u0 @x1 @x2))
    :qid typing_FStar.List.Tot.Base.tl))
  :named typing_FStar.List.Tot.Base.tl))
; free var typing
;;; Fact-ids: Name FStar.Seq.Base.seq_to_list; Namespace FStar.Seq.Base
(assert
 (! ;; def=FStar.Seq.Base.fsti(28,4-28,15); use=FStar.Seq.Base.fsti(28,4-28,15)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)))
     (HasType
      (FStar.Seq.Base.seq_to_list @u0 @x1 @x2)
      (Tm_refine_97286b406018c8659cdb053df840f284 @u0 @x1 @x2)))
    :pattern ((FStar.Seq.Base.seq_to_list @u0 @x1 @x2))
    :qid typing_FStar.Seq.Base.seq_to_list))
  :named typing_FStar.Seq.Base.seq_to_list))
; free var typing
;;; Fact-ids: Name FStar.Seq.Properties.snoc; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(316,4-316,8); use=FStar.Seq.Properties.fsti(316,4-316,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (FStar.Seq.Base.seq @u0 @x1)) (HasType @x3 @x1))
     (HasType (FStar.Seq.Properties.snoc @u0 @x1 @x2 @x3) (FStar.Seq.Base.seq @u0 @x1)))
    :pattern ((FStar.Seq.Properties.snoc @u0 @x1 @x2 @x3))
    :qid typing_FStar.Seq.Properties.snoc))
  :named typing_FStar.Seq.Properties.snoc))
; free var typing
;;; Fact-ids: Name Prims.eq2; Namespace Prims
(assert
 (! ;; def=Prims.fst(183,5-183,8); use=Prims.fst(183,5-183,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 @x1) (HasType @x3 @x1))
     (HasType (Prims.eq2 @u0 @x1 @x2 @x3) Prims.logical))
    :pattern ((Prims.eq2 @u0 @x1 @x2 @x3))
    :qid typing_Prims.eq2))
  :named typing_Prims.eq2))
; free var typing
;;; Fact-ids: Name Prims.uu___is_Cons; Namespace Prims
(assert
 (! ;; def=Prims.fst(618,4-618,8); use=Prims.fst(618,4-618,8)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 (Tm_type @u0)) (HasType @x2 (Prims.list @u0 @x1)))
     (HasType (Prims.uu___is_Cons @u0 @x1 @x2) Prims.bool))
    :pattern ((Prims.uu___is_Cons @u0 @x1 @x2))
    :qid typing_Prims.uu___is_Cons))
  :named typing_Prims.uu___is_Cons))
(push) ;; push{2
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_9d66f4024b4d68a20c027440b979f12e (Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60); use=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named refinement_kinding_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60); use=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x2))
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero @x2))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(68,42-68,58); use=Pulse.Spec.GC.GraphBridge.fst(68,42-68,58)
      (> (BoxInt_proj_0 (FStar.Seq.Base.length U_zero @x2 @x1)) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x2)))
    :qid refinement_interpretation_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named refinement_interpretation_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
; haseq for Tm_refine_9d66f4024b4d68a20c027440b979f12e
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60); use=Pulse.Spec.GC.GraphBridge.fst(68,32-68,60)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0)))
     (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero @x0))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0))))
    :qid haseqTm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named haseqTm_refine_9d66f4024b4d68a20c027440b979f12e))
; Encoding query formula : forall (a: Prims.eqtype) (s: FStar.Seq.Base.seq a {FStar.Seq.Base.length s > 0}).
;   (* - Could not prove post-condition *)
;   forall (p: Prims.pure_post Prims.unit).
;     (forall (pure_result: Prims.unit).
;         FStar.Seq.Properties.mem (FStar.Seq.Properties.head s) s ==> p pure_result) ==>
;     (forall (pure_result: Prims.unit).
;         (forall (y: a).
;             FStar.Seq.Properties.mem y
;               (FStar.Seq.Properties.snoc (FStar.Seq.Properties.tail s) (FStar.Seq.Properties.head s)
;               ) <==>
;             FStar.Seq.Properties.mem y (FStar.Seq.Properties.tail s) \/
;             FStar.Seq.Properties.head s = y) ==>
;         0 < FStar.Seq.Base.length s /\
;         (forall (any_result: Prims.int).
;             0 == any_result ==>
;             (forall (any_result: a).
;                 FStar.Seq.Base.index s 0 == any_result ==>
;                 (forall (any_result: Prims.logical).
;                     FStar.Seq.Properties.head s == FStar.Seq.Base.index s 0 == any_result ==>
;                     FStar.Seq.Properties.head s == FStar.Seq.Base.index s 0 /\
;                     (forall (pure_result: Prims.unit).
;                         FStar.Seq.Properties.head s == FStar.Seq.Base.index s 0 ==>
;                         0 < FStar.Seq.Base.length s /\
;                         (forall (any_result: Prims.int).
;                             0 == any_result ==>
;                             (forall (pure_result: Prims.unit).
;                                 FStar.List.Tot.Base.index (FStar.Seq.Base.seq_to_list s) 0 ==
;                                 FStar.Seq.Base.index s 0 ==>
;                                 p pure_result)))))))
; Context: While encoding a query
; While typechecking the top-level declaration `let head_is_member`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.eqtype) (HasType @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0)))
      ;; def=Prims.fst(414,51-414,91); use=Prims.fst(438,19-438,32)
      (forall ((@x2 Term))
       (! (implies
         (and
          (HasType @x2 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
          (forall ((@x3 Term))
           (! (implies
             (and
              (or label_1 (HasType @x3 Prims.unit))
              ;; def=Pulse.Spec.GC.GraphBridge.fst(69,10-69,34); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
              (or
               label_2
               ;; def=Pulse.Spec.GC.GraphBridge.fst(69,10-69,34); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
               (BoxBool_proj_0
                (FStar.Seq.Properties.mem @x0 (FStar.Seq.Properties.head U_zero @x0 @x1) @x1))))
             ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
             (Valid
              ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
              (ApplyTT @x2 @x3)))
            :pattern
             (;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
              (Valid
               ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
               (ApplyTT @x2 @x3)))
            :qid @query.2)))
         ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
         (forall ((@x3 Term))
          (! (implies
            (and
             (HasType @x3 Prims.unit)
             ;; def=FStar.Seq.Properties.fsti(331,18-331,66); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
             (forall ((@x4 Term))
              (! (implies
                (HasType @x4 @x0)
                ;; def=FStar.Seq.Properties.fsti(331,29-331,65); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
                (iff
                 ;; def=FStar.Seq.Properties.fsti(331,29-331,45); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
                 (BoxBool_proj_0
                  (FStar.Seq.Properties.mem
                   @x0
                   @x4
                   (FStar.Seq.Properties.snoc
                    U_zero
                    @x0
                    (FStar.Seq.Properties.tail U_zero @x0 @x1)
                    (FStar.Seq.Properties.head U_zero @x0 @x1))))
                 ;; def=FStar.Seq.Properties.fsti(331,51-331,65); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
                 (or
                  ;; def=FStar.Seq.Properties.fsti(331,51-331,58); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
                  (BoxBool_proj_0
                   (FStar.Seq.Properties.mem @x0 @x4 (FStar.Seq.Properties.tail U_zero @x0 @x1)))
                  ;; def=FStar.Seq.Properties.fsti(331,62-331,65); use=Pulse.Spec.GC.GraphBridge.fst(70,8-70,22)
                  (= (FStar.Seq.Properties.head U_zero @x0 @x1) @x4))))
               :qid @query.4)))
            ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
            (and
             ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=Pulse.Spec.GC.GraphBridge.fst(71,38-71,39)
             (or
              label_3
              ;; def=FStar.Seq.Base.fsti(32,40-32,52); use=Pulse.Spec.GC.GraphBridge.fst(71,38-71,39)
              (< (BoxInt_proj_0 (BoxInt 0)) (BoxInt_proj_0 (FStar.Seq.Base.length U_zero @x0 @x1))))
             ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
             (forall ((@x4 Term))
              (! (implies
                (and
                 (HasType @x4 Prims.int)
                 ;; def=FStar.Seq.Base.fsti(32,34-32,35); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                 (= (BoxInt 0) @x4))
                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                (forall ((@x5 Term))
                 (! (implies
                   (and
                    (HasType @x5 @x0)
                    ;; def=Prims.fst(183,42-183,43); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                    (= (FStar.Seq.Base.index U_zero @x0 @x1 (BoxInt 0)) @x5))
                   ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                   (forall ((@x6 Term))
                    (! (implies
                      (and
                       (HasType @x6 Prims.logical)
                       ;; def=Prims.fst(674,13-674,14); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                       (=
                        (Prims.eq2
                         U_zero
                         @x0
                         (FStar.Seq.Properties.head U_zero @x0 @x1)
                         (FStar.Seq.Base.index U_zero @x0 @x1 (BoxInt 0)))
                        @x6))
                      ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(71,4-71,10)
                      (and
                       ;; def=Pulse.Spec.GC.GraphBridge.fst(71,11-71,40); use=Pulse.Spec.GC.GraphBridge.fst(71,4-71,10)
                       (or
                        label_4
                        ;; def=Pulse.Spec.GC.GraphBridge.fst(71,11-71,40); use=Pulse.Spec.GC.GraphBridge.fst(71,4-71,10)
                        (=
                         (FStar.Seq.Properties.head U_zero @x0 @x1)
                         (FStar.Seq.Base.index U_zero @x0 @x1 (BoxInt 0))))
                       ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(71,4-71,10)
                       (forall ((@x7 Term))
                        (! (implies
                          (and
                           (HasType @x7 Prims.unit)
                           ;; def=Pulse.Spec.GC.GraphBridge.fst(71,11-71,40); use=Pulse.Spec.GC.GraphBridge.fst(71,4-71,10)
                           (=
                            (FStar.Seq.Properties.head U_zero @x0 @x1)
                            (FStar.Seq.Base.index U_zero @x0 @x1 (BoxInt 0))))
                          ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                          (and
                           ;; def=FStar.Seq.Properties.fsti(455,52-455,64); use=Pulse.Spec.GC.GraphBridge.fst(72,29-72,30)
                           (or
                            label_5
                            ;; def=FStar.Seq.Properties.fsti(455,52-455,64); use=Pulse.Spec.GC.GraphBridge.fst(72,29-72,30)
                            (<
                             (BoxInt_proj_0 (BoxInt 0))
                             (BoxInt_proj_0 (FStar.Seq.Base.length U_zero @x0 @x1))))
                           ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                           (forall ((@x8 Term))
                            (! (implies
                              (and
                               (HasType @x8 Prims.int)
                               ;; def=FStar.Seq.Properties.fsti(455,46-455,47); use=Pulse.Spec.GC.GraphBridge.fst(70,4-72,30)
                               (= (BoxInt 0) @x8))
                              ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(72,8-72,26)
                              (forall ((@x9 Term))
                               (! (implies
                                 (and
                                  (HasType @x9 Prims.unit)
                                  ;; def=FStar.Seq.Properties.fsti(457,12-457,52); use=Pulse.Spec.GC.GraphBridge.fst(72,8-72,26)
                                  (=
                                   (FStar.List.Tot.Base.index
                                    U_zero
                                    @x0
                                    (FStar.Seq.Base.seq_to_list U_zero @x0 @x1)
                                    (BoxInt 0))
                                   (FStar.Seq.Base.index U_zero @x0 @x1 (BoxInt 0))))
                                 ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(72,8-72,26)
                                 (Valid
                                  ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(72,8-72,26)
                                  (ApplyTT @x2 @x9)))
                                :qid @query.10)))
                             :qid @query.9))))
                         :qid @query.8))))
                     :qid @query.7)))
                  :qid @query.6)))
               :qid @query.5))))
           :qid @query.3)))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.head_is_member, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(push) ;; push{2
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_9d66f4024b4d68a20c027440b979f12e (Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57); use=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named refinement_kinding_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57); use=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x2))
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero @x2))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(75,39-75,55); use=Pulse.Spec.GC.GraphBridge.fst(75,39-75,55)
      (> (BoxInt_proj_0 (FStar.Seq.Base.length U_zero @x2 @x1)) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x2)))
    :qid refinement_interpretation_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named refinement_interpretation_Tm_refine_9d66f4024b4d68a20c027440b979f12e))
; haseq for Tm_refine_9d66f4024b4d68a20c027440b979f12e
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57); use=Pulse.Spec.GC.GraphBridge.fst(75,29-75,57)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0)))
     (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero @x0))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0))))
    :qid haseqTm_refine_9d66f4024b4d68a20c027440b979f12e))
  :named haseqTm_refine_9d66f4024b4d68a20c027440b979f12e))
; Encoding query formula : forall (a: Prims.eqtype) (s: FStar.Seq.Base.seq a {FStar.Seq.Base.length s > 0}) (x: a).
;   (* - Could not prove post-condition *)
;   forall (p: Prims.pure_post Prims.unit).
;     (forall (pure_result: Prims.unit).
;         (FStar.Seq.Properties.mem x (FStar.Seq.Properties.tail s) ==> FStar.Seq.Properties.mem x s) ==>
;         p pure_result) ==>
;     (forall (k: Prims.pure_post Prims.unit).
;         (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;         (FStar.Seq.Properties.mem x (FStar.Seq.Properties.tail s) == true ==>
;           (forall (pure_result: Prims.unit).
;               (forall (x: a).
;                   FStar.Seq.Properties.count x
;                     (FStar.Seq.Base.append (FStar.Seq.Base.create 1 (FStar.Seq.Properties.head s))
;                         (FStar.Seq.Properties.tail s)) =
;                   FStar.Seq.Properties.count x
;                     (FStar.Seq.Base.create 1 (FStar.Seq.Properties.head s)) +
;                   FStar.Seq.Properties.count x (FStar.Seq.Properties.tail s)) ==>
;               k pure_result)) /\
;         (~(FStar.Seq.Properties.mem x (FStar.Seq.Properties.tail s) = true) ==>
;           (forall (b: Prims.bool).
;               FStar.Seq.Properties.mem x (FStar.Seq.Properties.tail s) == b ==>
;               (forall (any_result: Prims.unit). k any_result))))
; Context: While encoding a query
; While typechecking the top-level declaration `let tail_subset`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term) (@x2 Term))
    (! (implies
      (and
       (HasType @x0 Prims.eqtype)
       (HasType @x1 (Tm_refine_9d66f4024b4d68a20c027440b979f12e @x0))
       (HasType @x2 @x0))
      ;; def=Prims.fst(414,51-414,91); use=Prims.fst(438,19-438,32)
      (forall ((@x3 Term))
       (! (implies
         (and
          (HasType @x3 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
          (forall ((@x4 Term))
           (! (implies
             (and
              (or label_1 (HasType @x4 Prims.unit))
              (implies
               ;; def=Pulse.Spec.GC.GraphBridge.fst(76,11-76,33); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
               (BoxBool_proj_0
                (FStar.Seq.Properties.mem @x0 @x2 (FStar.Seq.Properties.tail U_zero @x0 @x1)))
               ;; def=Pulse.Spec.GC.GraphBridge.fst(76,38-76,49); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
               (or
                label_2
                ;; def=Pulse.Spec.GC.GraphBridge.fst(76,38-76,49); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                (BoxBool_proj_0 (FStar.Seq.Properties.mem @x0 @x2 @x1)))))
             ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
             (Valid
              ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
              (ApplyTT @x3 @x4)))
            :pattern
             (;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
              (Valid
               ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
               (ApplyTT @x3 @x4)))
            :qid @query.2)))
         ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
         (forall ((@x4 Term))
          (! (implies
            (and
             (HasType @x4 (Prims.pure_post U_zero Prims.unit))
             ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
             (forall ((@x5 Term))
              (! (implies
                ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                (Valid
                 ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                 (ApplyTT @x3 @x5))
                ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                (Valid
                 ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                 (ApplyTT @x4 @x5)))
               :weight 0
               :pattern ((ApplyTT @x4 @x5))
               :qid @query.4)))
            ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
            (and
             (implies
              ;; def=Pulse.Spec.GC.GraphBridge.fst(77,7-77,29); use=Pulse.Spec.GC.GraphBridge.fst(77,7-77,29)
              (=
               (FStar.Seq.Properties.mem @x0 @x2 (FStar.Seq.Properties.tail U_zero @x0 @x1))
               (BoxBool true))
              ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(78,27-78,45)
              (forall ((@x5 Term))
               (! (implies
                 (and
                  (HasType @x5 Prims.unit)
                  ;; def=FStar.Seq.Properties.fsti(138,11-138,73); use=Pulse.Spec.GC.GraphBridge.fst(78,27-78,45)
                  (forall ((@x6 Term))
                   (! (implies
                     (HasType @x6 @x0)
                     ;; def=FStar.Seq.Properties.fsti(138,22-138,72); use=Pulse.Spec.GC.GraphBridge.fst(78,27-78,45)
                     (=
                      (FStar.Seq.Properties.count
                       @x0
                       @x6
                       (FStar.Seq.Base.append
                        U_zero
                        @x0
                        (FStar.Seq.Base.create
                         U_zero
                         @x0
                         (BoxInt 1)
                         (FStar.Seq.Properties.head U_zero @x0 @x1))
                        (FStar.Seq.Properties.tail U_zero @x0 @x1)))
                      (Prims.op_Addition
                       (FStar.Seq.Properties.count
                        @x0
                        @x6
                        (FStar.Seq.Base.create
                         U_zero
                         @x0
                         (BoxInt 1)
                         (FStar.Seq.Properties.head U_zero @x0 @x1)))
                       (FStar.Seq.Properties.count
                        @x0
                        @x6
                        (FStar.Seq.Properties.tail U_zero @x0 @x1)))))
                    :qid @query.6)))
                 ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(78,27-78,45)
                 (Valid
                  ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(78,27-78,45)
                  (ApplyTT @x4 @x5)))
                :qid @query.5)))
             (implies
              ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
              (not
               ;; def=Pulse.Spec.GC.GraphBridge.fst(77,7-77,29); use=Pulse.Spec.GC.GraphBridge.fst(77,7-77,29)
               (=
                (FStar.Seq.Properties.mem @x0 @x2 (FStar.Seq.Properties.tail U_zero @x0 @x1))
                (BoxBool true)))
              ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
              (forall ((@x5 Term))
               (! (implies
                 (and
                  (HasType @x5 Prims.bool)
                  ;; def=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                  (=
                   (FStar.Seq.Properties.mem @x0 @x2 (FStar.Seq.Properties.tail U_zero @x0 @x1))
                   @x5))
                 ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                 (forall ((@x6 Term))
                  (! (implies
                    (HasType @x6 Prims.unit)
                    ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                    (Valid
                     ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(77,4-78,86)
                     (ApplyTT @x4 @x6)))
                   :qid @query.8)))
                :qid @query.7)))))
           :qid @query.3)))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.tail_subset, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun FStar.UInt.add_mod (Term Term Term) Term)
(declare-fun FStar.UInt64.add_mod (Term Term) Term)
(declare-fun Prims.l_imp (Term Term) Term)
(declare-fun Prims.op_BarBar (Term Term) Term)
(declare-fun Pulse.Spec.GC.Fields.obj_address (Term) Term)
(declare-fun Pulse.Spec.GC.Fields.objects (Term Term) Term)
; Fuel-instrumented function name
(declare-fun Pulse.Spec.GC.Fields.objects.fuel_instrumented (Fuel Term Term) Term)
(declare-fun Pulse.Spec.GC.GraphBridge.all_objects_well_formed (Term) Term)
(declare-fun Pulse.Spec.GC.GraphBridge.collect_edges_from_object (Term Term Term Term) Term)
; Fuel-instrumented function name
(declare-fun
 Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
 (Fuel Term Term Term Term)
 Term)
(declare-fun Pulse.Spec.GC.GraphBridge.objs_subset_of_objects (Term Term) Term)
(declare-fun Pulse.Spec.GC.Object.getWosize (Term) Term)
(declare-fun Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e (Term Term) Term)
(declare-fun Tm_refine_2d98f2f5de361516da3dbd9f556509e2 (Term Term) Term)
(declare-fun Tm_refine_342151ed351c78dc8ce598768ff63d17 () Term)
(declare-fun Tm_refine_5542e74c2098708b2a57cce4179a9c2e (Universe Term Term Term) Term)
(declare-fun Tm_refine_ddd44b85040d1947cca83550b7e21966 (Term) Term)
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name Pulse.Spec.GC.Fields.objects; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(138,8-138,15); use=Pulse.Spec.GC.Fields.fst(138,8-138,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Pulse.Spec.GC.Fields.objects @x0 @x1)
     (Pulse.Spec.GC.Fields.objects.fuel_instrumented MaxFuel @x0 @x1))
    :pattern ((Pulse.Spec.GC.Fields.objects @x0 @x1))
    :qid @fuel_correspondence_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
  :named @fuel_correspondence_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (=
     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3)
     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented MaxFuel @x0 @x1 @x2 @x3))
    :pattern ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3))
    :qid @fuel_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
  :named @fuel_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name Pulse.Spec.GC.Fields.objects; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(138,8-138,15); use=Pulse.Spec.GC.Fields.fst(138,8-138,15)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (=
     (Pulse.Spec.GC.Fields.objects.fuel_instrumented (SFuel @u0) @x1 @x2)
     (Pulse.Spec.GC.Fields.objects.fuel_instrumented ZFuel @x1 @x2))
    :pattern ((Pulse.Spec.GC.Fields.objects.fuel_instrumented (SFuel @u0) @x1 @x2))
    :qid @fuel_irrelevance_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
  :named @fuel_irrelevance_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
      (SFuel @u0)
      @x1
      @x2
      @x3
      @x4)
     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented ZFuel @x1 @x2 @x3 @x4))
    :pattern
     ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
       (SFuel @u0)
       @x1
       @x2
       @x3
       @x4))
    :qid @fuel_irrelevance_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
  :named @fuel_irrelevance_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
; interpretation_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! ;; def=Prims.fst(212,12-212,26); use=Prims.fst(212,57-212,68)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x1 @x2))
     ;; def=Prims.fst(212,12-212,26); use=Prims.fst(212,57-212,68)
     (forall ((@x3 Term))
      (! (implies (HasType @x3 @x1) (HasType (ApplyTT @x0 @x3) @x2))
       :pattern ((ApplyTT @x0 @x3))
       :qid Prims_interpretation_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e.1)))
    :pattern ((HasTypeZ @x0 (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x1 @x2)))
    :qid Prims_interpretation_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
  :named Prims_interpretation_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
; pre-typing for functions
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! ;; def=Prims.fst(212,12-212,26); use=Prims.fst(212,57-212,68)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x2 @x3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x2 @x3)))
    :qid Prims_pre_typing_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
  :named Prims_pre_typing_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
; Prop-typing for Pulse.Spec.GC.GraphBridge.all_objects_well_formed
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.all_objects_well_formed; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27); use=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Spec.GC.Base.heap)
     (Valid
      (Prims.subtype_of
       U_zero
       U_zero
       (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0)
       Prims.unit)))
    :pattern
     ((Prims.subtype_of
       U_zero
       U_zero
       (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0)
       Prims.unit))
    :qid defn_equation_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
  :named defn_equation_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
; Prop-typing for Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.objs_subset_of_objects; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26); use=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      (HasType @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr)))
     (Valid
      (Prims.subtype_of
       U_zero
       U_zero
       (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1)
       Prims.unit)))
    :pattern
     ((Prims.subtype_of
       U_zero
       U_zero
       (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1)
       Prims.unit))
    :qid defn_equation_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
  :named defn_equation_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
; Equation for FStar.UInt.add_mod
;;; Fact-ids: Name FStar.UInt.add_mod; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(99,4-99,11); use=FStar.UInt.fsti(99,4-99,11)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (=
     (FStar.UInt.add_mod @x0 @x1 @x2)
     (Prims.op_Modulus (Prims.op_Addition @x1 @x2) (Prims.pow2 @x0)))
    :pattern ((FStar.UInt.add_mod @x0 @x1 @x2))
    :qid equation_FStar.UInt.add_mod))
  :named equation_FStar.UInt.add_mod))
; Equation for Prims.l_imp
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! ;; def=Prims.fst(212,5-212,10); use=Prims.fst(212,5-212,10)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Prims.l_imp @x0 @x1)
     (Prims.squash U_zero (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x0 @x1)))
    :pattern ((Prims.l_imp @x0 @x1))
    :qid equation_Prims.l_imp))
  :named equation_Prims.l_imp))
; Equation for Pulse.Spec.GC.Fields.obj_address
;;; Fact-ids: Name Pulse.Spec.GC.Fields.obj_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(36,4-36,15); use=Pulse.Spec.GC.Fields.fst(36,4-36,15)
  (forall ((@x0 Term))
   (! (=
     (Pulse.Spec.GC.Fields.obj_address @x0)
     (FStar.UInt64.add_mod @x0 (Pulse.Spec.GC.Base.mword Dummy_value)))
    :pattern ((Pulse.Spec.GC.Fields.obj_address @x0))
    :qid equation_Pulse.Spec.GC.Fields.obj_address))
  :named equation_Pulse.Spec.GC.Fields.obj_address))
; Equation for Pulse.Spec.GC.GraphBridge.all_objects_well_formed
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.all_objects_well_formed; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27); use=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27)
  (forall ((@x0 Term))
   (! (=
     (Valid (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0))
     ;; def=Pulse.Spec.GC.GraphBridge.fst(61,2-61,75); use=Pulse.Spec.GC.GraphBridge.fst(61,2-61,75)
     (forall ((@x1 Term))
      (! (implies
        (and
         (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
         ;; def=Pulse.Spec.GC.GraphBridge.fst(61,23-61,48); use=Pulse.Spec.GC.GraphBridge.fst(61,23-61,48)
         (BoxBool_proj_0
          (FStar.Seq.Properties.mem
           Pulse.Spec.GC.Base.hp_addr
           @x1
           (Pulse.Spec.GC.Fields.objects (FStar.UInt64.uint_to_t (BoxInt 0)) @x0))))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(61,53-61,75); use=Pulse.Spec.GC.GraphBridge.fst(61,53-61,75)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(61,53-61,75); use=Pulse.Spec.GC.GraphBridge.fst(61,53-61,75)
         (Pulse.Spec.GC.Fields.well_formed_object @x0 @x1)))
       :qid equation_Pulse.Spec.GC.GraphBridge.all_objects_well_formed.1)))
    :pattern ((Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0))
    :qid equation_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
  :named equation_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
; Equation for Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.objs_subset_of_objects; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26); use=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Valid (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1))
     ;; def=Pulse.Spec.GC.GraphBridge.fst(65,2-65,67); use=Pulse.Spec.GC.GraphBridge.fst(65,2-65,67)
     (forall ((@x2 Term))
      (! (implies
        (and
         (HasType @x2 Pulse.Spec.GC.Base.hp_addr)
         ;; def=Pulse.Spec.GC.GraphBridge.fst(65,23-65,37); use=Pulse.Spec.GC.GraphBridge.fst(65,23-65,37)
         (BoxBool_proj_0 (FStar.Seq.Properties.mem Pulse.Spec.GC.Base.hp_addr @x2 @x1)))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(65,42-65,67); use=Pulse.Spec.GC.GraphBridge.fst(65,42-65,67)
        (BoxBool_proj_0
         (FStar.Seq.Properties.mem
          Pulse.Spec.GC.Base.hp_addr
          @x2
          (Pulse.Spec.GC.Fields.objects (FStar.UInt64.uint_to_t (BoxInt 0)) @x0))))
       :qid equation_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects.1)))
    :pattern ((Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1))
    :qid equation_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
  :named equation_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
; Equation for fuel-instrumented recursive function: Pulse.Spec.GC.Fields.objects
;;; Fact-ids: Name Pulse.Spec.GC.Fields.objects; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(138,8-138,15); use=Pulse.Spec.GC.Fields.fst(138,8-138,15)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 Pulse.Spec.GC.Base.hp_addr) (HasType @x2 Pulse.Spec.GC.Base.heap))
     (=
      (Pulse.Spec.GC.Fields.objects.fuel_instrumented (SFuel @u0) @x1 @x2)
      (let
        ((@lb3
          (Prims.op_GreaterThanOrEqual
           (Prims.op_Addition (FStar.UInt64.v @x1) (BoxInt 8))
           (FStar.Seq.Base.length U_zero (FStar.UInt8.t Dummy_value) @x2))))
       (ite
        (= @lb3 (BoxBool true))
        (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Base.hp_addr)
        (let
          ((@lb4
            (Prims.op_BarBar
             (Prims.op_GreaterThan
              (Prims.op_Addition
               (FStar.UInt64.v @x1)
               (Prims.op_Multiply
                (Prims.op_Addition
                 (FStar.UInt64.v
                  (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word @x2 @x1)))
                 (BoxInt 1))
                (BoxInt 8)))
              (FStar.Seq.Base.length U_zero (FStar.UInt8.t Dummy_value) @x2))
             (Prims.op_GreaterThanOrEqual
              (Prims.op_Addition
               (FStar.UInt64.v @x1)
               (Prims.op_Multiply
                (Prims.op_Addition
                 (FStar.UInt64.v
                  (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word @x2 @x1)))
                 (BoxInt 1))
                (BoxInt 8)))
              (Prims.pow2 (BoxInt 64))))))
         (ite
          (= @lb4 (BoxBool true))
          (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Base.hp_addr)
          (let
            ((@lb5
              (Prims.op_GreaterThanOrEqual
               (Prims.op_Addition
                (FStar.UInt64.v @x1)
                (Prims.op_Multiply
                 (Prims.op_Addition
                  (FStar.UInt64.v
                   (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word @x2 @x1)))
                  (BoxInt 1))
                 (BoxInt 8)))
               (Pulse.Spec.GC.Base.heap_size Dummy_value))))
           (ite
            (= @lb5 (BoxBool true))
            (FStar.Seq.Base.cons
             U_zero
             Pulse.Spec.GC.Base.hp_addr
             (Pulse.Spec.GC.Fields.obj_address @x1)
             (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Base.hp_addr))
            (FStar.Seq.Base.cons
             U_zero
             Pulse.Spec.GC.Base.hp_addr
             (Pulse.Spec.GC.Fields.obj_address @x1)
             (Pulse.Spec.GC.Fields.objects.fuel_instrumented
              @u0
              (FStar.UInt64.uint_to_t
               (Prims.op_Addition
                (FStar.UInt64.v @x1)
                (Prims.op_Multiply
                 (Prims.op_Addition
                  (FStar.UInt64.v
                   (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word @x2 @x1)))
                  (BoxInt 1))
                 (BoxInt 8))))
              @x2))))))))))
    :weight 0
    :pattern ((Pulse.Spec.GC.Fields.objects.fuel_instrumented (SFuel @u0) @x1 @x2))
    :qid equation_with_fuel_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
  :named equation_with_fuel_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
; Equation for fuel-instrumented recursive function: Pulse.Spec.GC.GraphBridge.collect_edges_from_object
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 Pulse.Spec.GC.Base.heap)
      (HasType @x2 Pulse.Spec.GC.Base.hp_addr)
      (HasType @x3 Pulse.Spec.GC.Fields.wosize)
      (HasType @x4 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
       (Pulse.Spec.GC.Fields.well_formed_object @x1 @x2))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84)
      (<=
       (BoxInt_proj_0 (FStar.UInt64.v @x3))
       (BoxInt_proj_0 (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x2 @x1)))))
     (=
      (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
       (SFuel @u0)
       @x1
       @x2
       @x3
       @x4)
      (let ((@lb5 (Prims.op_GreaterThanOrEqual (FStar.UInt64.v @x4) (FStar.UInt64.v @x3))))
       (ite
        (= @lb5 (BoxBool true))
        (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)
        (let
          ((@lb6
            (Prims.op_AmpAmp
             (Pulse.Spec.GC.Fields.is_pointer_field
              (Pulse.Spec.GC.Heap.read_word @x1 (Pulse.Spec.GC.Fields.field_address @x2 @x4)))
             (Prims.op_disEquality
              (FStar.UInt64.t Dummy_value)
              (Pulse.Spec.GC.Heap.read_word @x1 (Pulse.Spec.GC.Fields.field_address @x2 @x4))
              (FStar.UInt64.uint_to_t (BoxInt 0))))))
         (ite
          (= @lb6 (BoxBool true))
          (FStar.Seq.Base.cons
           U_zero
           Pulse.Spec.GC.Graph.edge
           (FStar.Pervasives.Native.Mktuple2
            U_zero
            U_zero
            Pulse.Spec.GC.Graph.vertex_id
            Pulse.Spec.GC.Graph.vertex_id
            @x2
            (Pulse.Spec.GC.Heap.read_word @x1 (Pulse.Spec.GC.Fields.field_address @x2 @x4)))
           (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
            @u0
            @x1
            @x2
            @x3
            (FStar.UInt64.add @x4 (FStar.UInt64.uint_to_t (BoxInt 1)))))
          (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
           @u0
           @x1
           @x2
           @x3
           (FStar.UInt64.add @x4 (FStar.UInt64.uint_to_t (BoxInt 1))))))))))
    :weight 0
    :pattern
     ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented
       (SFuel @u0)
       @x1
       @x2
       @x3
       @x4))
    :qid equation_with_fuel_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
  :named equation_with_fuel_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
; haseq for Tm_refine_2d98f2f5de361516da3dbd9f556509e2
;;; Fact-ids: Name FStar.UInt64.add_mod; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(105,31-105,32); use=FStar.UInt64.fsti(105,31-105,32)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x0 @x1)))
     (Valid (Prims.hasEq U_zero (FStar.UInt64.t Dummy_value))))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x0 @x1))))
    :qid haseqTm_refine_2d98f2f5de361516da3dbd9f556509e2))
  :named haseqTm_refine_2d98f2f5de361516da3dbd9f556509e2))
; haseq for Tm_refine_342151ed351c78dc8ce598768ff63d17
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_342151ed351c78dc8ce598768ff63d17))
   (Valid (Prims.hasEq U_zero Pulse.Spec.GC.Graph.edge_list)))
  :named haseqTm_refine_342151ed351c78dc8ce598768ff63d17))
; haseq for Tm_refine_5542e74c2098708b2a57cce4179a9c2e
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(595,2-595,36); use=FStar.Seq.Properties.fsti(595,2-595,36)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u0 @x1 @x2 @x3)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern
     ((Valid (Prims.hasEq U_zero (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u0 @x1 @x2 @x3))))
    :qid haseqTm_refine_5542e74c2098708b2a57cce4179a9c2e))
  :named haseqTm_refine_5542e74c2098708b2a57cce4179a9c2e))
; haseq for Tm_refine_ddd44b85040d1947cca83550b7e21966
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(596,2-596,19); use=FStar.Seq.Properties.fsti(596,2-596,19)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x0)))
     (Valid (Prims.hasEq U_zero Prims.nat)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x0))))
    :qid haseqTm_refine_ddd44b85040d1947cca83550b7e21966))
  :named haseqTm_refine_ddd44b85040d1947cca83550b7e21966))
; kinding_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! ;; def=Prims.fst(212,12-212,26); use=Prims.fst(212,57-212,68)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e @x0 @x1) (Tm_type U_zero)))
    :qid kinding_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
  :named kinding_Tm_ghost_arrow_9028fac21fb10f6bfa48c18673a1620e))
; ==> interpretation
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! (forall ((@x0 Term) (@x1 Term))
   (! (iff (implies (Valid @x0) (Valid @x1)) (Valid (Prims.l_imp @x0 @x1)))
    :pattern ((Prims.l_imp @x0 @x1))
    :qid l_imp-interp))
  :named l_imp-interp))
; Lemma: FStar.Seq.Properties.cons_head_tail
;;; Fact-ids: Name FStar.Seq.Properties.cons_head_tail; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (Tm_refine_b941dbc92f527a1ccce4d1a02373e9c1 @u0 @x1)))
     ;; def=FStar.Seq.Properties.fsti(527,11-527,40); use=FStar.Seq.Properties.fsti(527,11-527,40)
     (=
      @x2
      (FStar.Seq.Base.cons
       @u0
       @x1
       (FStar.Seq.Properties.head @u0 @x1 @x2)
       (FStar.Seq.Properties.tail @u0 @x1 @x2))))
    :pattern
     ((FStar.Seq.Base.cons
       @u0
       @x1
       (FStar.Seq.Properties.head @u0 @x1 @x2)
       (FStar.Seq.Properties.tail @u0 @x1 @x2)))
    :qid lemma_FStar.Seq.Properties.cons_head_tail))
  :named lemma_FStar.Seq.Properties.cons_head_tail))
; Lemma: FStar.Seq.Properties.cons_index_slice
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (implies
     (and
      (HasType @x1 (Tm_type @u0))
      (HasType @x2 (FStar.Seq.Base.seq @u0 @x1))
      (HasType @x3 Prims.nat)
      (HasType @x4 (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u0 @x3 @x1 @x2))
      (HasType @x5 (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x3)))
     ;; def=FStar.Seq.Properties.fsti(599,11-599,58); use=FStar.Seq.Properties.fsti(599,11-599,58)
     (=
      (FStar.Seq.Base.cons
       @u0
       @x1
       (FStar.Seq.Base.index @u0 @x1 @x2 @x3)
       (FStar.Seq.Base.slice @u0 @x1 @x2 @x5 @x4))
      (FStar.Seq.Base.slice @u0 @x1 @x2 @x3 @x4)))
    :pattern
     ((FStar.Seq.Base.cons
       @u0
       @x1
       (FStar.Seq.Base.index @u0 @x1 @x2 @x3)
       (FStar.Seq.Base.slice @u0 @x1 @x2 @x5 @x4)))
    :qid lemma_FStar.Seq.Properties.cons_index_slice))
  :named lemma_FStar.Seq.Properties.cons_index_slice))
;;; Fact-ids: Name Prims.op_BarBar; Namespace Prims
(assert
 (! ;; def=Prims.fst(536,4-536,13); use=Prims.fst(536,4-536,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_BarBar @x0 @x1) (BoxBool (or (BoxBool_proj_0 @x0) (BoxBool_proj_0 @x1))))
    :pattern ((Prims.op_BarBar @x0 @x1))
    :qid primitive_Prims.op_BarBar))
  :named primitive_Prims.op_BarBar))
; refinement_interpretation
;;; Fact-ids: Name FStar.UInt64.add_mod; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(105,31-105,32); use=FStar.UInt64.fsti(105,31-105,32)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 (FStar.UInt64.t Dummy_value))
      ;; def=FStar.UInt64.fsti(107,21-107,57); use=FStar.UInt64.fsti(107,21-107,57)
      (=
       (FStar.UInt.add_mod (BoxInt 64) (FStar.UInt64.v @x2) (FStar.UInt64.v @x3))
       (FStar.UInt64.v @x1))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_2d98f2f5de361516da3dbd9f556509e2))
  :named refinement_interpretation_Tm_refine_2d98f2f5de361516da3dbd9f556509e2))
; refinement_interpretation
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(31,10-31,19); use=Pulse.Spec.GC.GraphBridge.fst(31,10-31,19)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_342151ed351c78dc8ce598768ff63d17)
     (HasTypeFuel @u0 @x1 Pulse.Spec.GC.Graph.edge_list))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :qid refinement_interpretation_Tm_refine_342151ed351c78dc8ce598768ff63d17))
  :named refinement_interpretation_Tm_refine_342151ed351c78dc8ce598768ff63d17))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(595,2-595,36); use=FStar.Seq.Properties.fsti(595,2-595,36)
  (forall ((@u0 Fuel) (@x1 Term) (@u2 Universe) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u2 @x3 @x4 @x5))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(595,11-595,16); use=FStar.Seq.Properties.fsti(595,11-595,16)
      (< (BoxInt_proj_0 @x3) (BoxInt_proj_0 @x1))
      ;; def=FStar.Seq.Properties.fsti(595,20-595,33); use=FStar.Seq.Properties.fsti(595,20-595,33)
      (<= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (FStar.Seq.Base.length @u2 @x4 @x5)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u2 @x3 @x4 @x5)))
    :qid refinement_interpretation_Tm_refine_5542e74c2098708b2a57cce4179a9c2e))
  :named refinement_interpretation_Tm_refine_5542e74c2098708b2a57cce4179a9c2e))
; refinement_interpretation
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(596,2-596,19); use=FStar.Seq.Properties.fsti(596,2-596,19)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=FStar.Seq.Properties.fsti(596,9-596,17); use=FStar.Seq.Properties.fsti(596,9-596,17)
      (= @x1 (Prims.op_Addition @x2 (BoxInt 1)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x2)))
    :qid refinement_interpretation_Tm_refine_ddd44b85040d1947cca83550b7e21966))
  :named refinement_interpretation_Tm_refine_ddd44b85040d1947cca83550b7e21966))
; refinement kinding
;;; Fact-ids: Name FStar.UInt64.add_mod; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(105,31-105,32); use=FStar.UInt64.fsti(105,31-105,32)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x0 @x1) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x0 @x1) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_2d98f2f5de361516da3dbd9f556509e2))
  :named refinement_kinding_Tm_refine_2d98f2f5de361516da3dbd9f556509e2))
; refinement kinding
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! (HasType Tm_refine_342151ed351c78dc8ce598768ff63d17 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_342151ed351c78dc8ce598768ff63d17))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(595,2-595,36); use=FStar.Seq.Properties.fsti(595,2-595,36)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (HasType (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u0 @x1 @x2 @x3) (Tm_type U_zero))
    :pattern
     ((HasType (Tm_refine_5542e74c2098708b2a57cce4179a9c2e @u0 @x1 @x2 @x3) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_5542e74c2098708b2a57cce4179a9c2e))
  :named refinement_kinding_Tm_refine_5542e74c2098708b2a57cce4179a9c2e))
; refinement kinding
;;; Fact-ids: Name FStar.Seq.Properties.cons_index_slice; Namespace FStar.Seq.Properties
(assert
 (! ;; def=FStar.Seq.Properties.fsti(596,2-596,19); use=FStar.Seq.Properties.fsti(596,2-596,19)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_ddd44b85040d1947cca83550b7e21966 @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_ddd44b85040d1947cca83550b7e21966))
  :named refinement_kinding_Tm_refine_ddd44b85040d1947cca83550b7e21966))
; Typing correspondence of token to term
;;; Fact-ids: Name Pulse.Spec.GC.Fields.objects; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(138,8-138,15); use=Pulse.Spec.GC.Fields.fst(138,8-138,15)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (implies
     (and (HasType @x1 Pulse.Spec.GC.Base.hp_addr) (HasType @x2 Pulse.Spec.GC.Base.heap))
     (HasType
      (Pulse.Spec.GC.Fields.objects.fuel_instrumented @u0 @x1 @x2)
      (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr)))
    :pattern ((Pulse.Spec.GC.Fields.objects.fuel_instrumented @u0 @x1 @x2))
    :qid token_correspondence_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
  :named token_correspondence_Pulse.Spec.GC.Fields.objects.fuel_instrumented))
; Typing correspondence of token to term
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
     (and
      (HasType @x1 Pulse.Spec.GC.Base.heap)
      (HasType @x2 Pulse.Spec.GC.Base.hp_addr)
      (HasType @x3 Pulse.Spec.GC.Fields.wosize)
      (HasType @x4 (FStar.UInt64.t Dummy_value))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
       (Pulse.Spec.GC.Fields.well_formed_object @x1 @x2))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84)
      (<=
       (BoxInt_proj_0 (FStar.UInt64.v @x3))
       (BoxInt_proj_0 (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x2 @x1)))))
     (HasType
      (Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented @u0 @x1 @x2 @x3 @x4)
      Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :pattern
     ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented @u0 @x1 @x2 @x3 @x4))
    :qid token_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
  :named token_correspondence_Pulse.Spec.GC.GraphBridge.collect_edges_from_object.fuel_instrumented))
; free var typing
;;; Fact-ids: Name FStar.UInt.add_mod; Namespace FStar.UInt
(assert
 (! ;; def=FStar.UInt.fsti(99,4-99,11); use=FStar.UInt.fsti(99,4-99,11)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasType @x0 Prims.nat)
      (HasType @x1 (FStar.UInt.uint_t @x0))
      (HasType @x2 (FStar.UInt.uint_t @x0)))
     (HasType (FStar.UInt.add_mod @x0 @x1 @x2) (FStar.UInt.uint_t @x0)))
    :pattern ((FStar.UInt.add_mod @x0 @x1 @x2))
    :qid typing_FStar.UInt.add_mod))
  :named typing_FStar.UInt.add_mod))
; free var typing
;;; Fact-ids: Name FStar.UInt64.add_mod; Namespace FStar.UInt64
(assert
 (! ;; def=FStar.UInt64.fsti(105,4-105,11); use=FStar.UInt64.fsti(105,4-105,11)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 (FStar.UInt64.t Dummy_value)) (HasType @x1 (FStar.UInt64.t Dummy_value)))
     (HasType (FStar.UInt64.add_mod @x0 @x1) (Tm_refine_2d98f2f5de361516da3dbd9f556509e2 @x0 @x1)))
    :pattern ((FStar.UInt64.add_mod @x0 @x1))
    :qid typing_FStar.UInt64.add_mod))
  :named typing_FStar.UInt64.add_mod))
; free var typing
;;; Fact-ids: Name Prims.l_imp; Namespace Prims
(assert
 (! ;; def=Prims.fst(212,5-212,10); use=Prims.fst(212,5-212,10)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.logical) (HasType @x1 Prims.logical))
     (HasType (Prims.l_imp @x0 @x1) Prims.logical))
    :pattern ((Prims.l_imp @x0 @x1))
    :qid typing_Prims.l_imp))
  :named typing_Prims.l_imp))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.obj_address; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(36,4-36,15); use=Pulse.Spec.GC.Fields.fst(36,4-36,15)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Spec.GC.Base.hp_addr)
     (HasType (Pulse.Spec.GC.Fields.obj_address @x0) (FStar.UInt64.t Dummy_value)))
    :pattern ((Pulse.Spec.GC.Fields.obj_address @x0))
    :qid typing_Pulse.Spec.GC.Fields.obj_address))
  :named typing_Pulse.Spec.GC.Fields.obj_address))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Fields.objects; Namespace Pulse.Spec.GC.Fields
(assert
 (! ;; def=Pulse.Spec.GC.Fields.fst(138,8-138,15); use=Pulse.Spec.GC.Fields.fst(138,8-138,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Pulse.Spec.GC.Base.hp_addr) (HasType @x1 Pulse.Spec.GC.Base.heap))
     (HasType
      (Pulse.Spec.GC.Fields.objects @x0 @x1)
      (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr)))
    :pattern ((Pulse.Spec.GC.Fields.objects @x0 @x1))
    :qid typing_Pulse.Spec.GC.Fields.objects))
  :named typing_Pulse.Spec.GC.Fields.objects))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.all_objects_well_formed; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27); use=Pulse.Spec.GC.GraphBridge.fst(60,4-60,27)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Spec.GC.Base.heap)
     (HasType (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0) Prims.prop))
    :pattern ((Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0))
    :qid typing_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
  :named typing_Pulse.Spec.GC.GraphBridge.all_objects_well_formed))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.collect_edges_from_object; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33); use=Pulse.Spec.GC.GraphBridge.fst(30,8-30,33)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38)
       (Pulse.Spec.GC.Fields.well_formed_object @x0 @x1))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84)
      (<=
       (BoxInt_proj_0 (FStar.UInt64.v @x2))
       (BoxInt_proj_0 (FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object @x1 @x0))))
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
      (HasType @x2 Pulse.Spec.GC.Fields.wosize)
      (HasType @x3 (FStar.UInt64.t Dummy_value)))
     (HasType
      (Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3)
      Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :pattern ((Pulse.Spec.GC.GraphBridge.collect_edges_from_object @x0 @x1 @x2 @x3))
    :qid typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
  :named typing_Pulse.Spec.GC.GraphBridge.collect_edges_from_object))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.GraphBridge.objs_subset_of_objects; Namespace Pulse.Spec.GC.GraphBridge
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26); use=Pulse.Spec.GC.GraphBridge.fst(64,4-64,26)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      (HasType @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr)))
     (HasType (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1) Prims.prop))
    :pattern ((Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1))
    :qid typing_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
  :named typing_Pulse.Spec.GC.GraphBridge.objs_subset_of_objects))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Object.getWosize; Namespace Pulse.Spec.GC.Object
(assert
 (! ;; def=Pulse.Spec.GC.Object.fsti(67,4-67,13); use=Pulse.Spec.GC.Object.fsti(67,4-67,13)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 (FStar.UInt64.t Dummy_value))
     (HasType (Pulse.Spec.GC.Object.getWosize @x0) (FStar.UInt64.t Dummy_value)))
    :pattern ((Pulse.Spec.GC.Object.getWosize @x0))
    :qid typing_Pulse.Spec.GC.Object.getWosize))
  :named typing_Pulse.Spec.GC.Object.getWosize))
(push) ;; push{2
; g : Pulse.Spec.GC.Base.heap (Pulse.Spec.GC.Base.heap)
(declare-fun x_e246fc25c9201731c203dc9e18738560_0 () Term)
; binder_x_e246fc25c9201731c203dc9e18738560_0
;;; Fact-ids: 
(assert
 (! (HasType x_e246fc25c9201731c203dc9e18738560_0 Pulse.Spec.GC.Base.heap)
  :named binder_x_e246fc25c9201731c203dc9e18738560_0))
; objs : FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr (FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr)
(declare-fun x_a43c9a43db9e9f97f09b6905c39a534e_1 () Term)
; binder_x_a43c9a43db9e9f97f09b6905c39a534e_1
;;; Fact-ids: 
(assert
 (! (HasType
   x_a43c9a43db9e9f97f09b6905c39a534e_1
   (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr))
  :named binder_x_a43c9a43db9e9f97f09b6905c39a534e_1))
(declare-fun Tm_refine_4a81764065a4360e3f4d7b2c4beaa311 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_4a81764065a4360e3f4d7b2c4beaa311 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,37-103,40); use=Pulse.Spec.GC.GraphBridge.fst(81,37-103,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_4a81764065a4360e3f4d7b2c4beaa311)
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
      ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
       (Prims.precedes
        U_zero
        U_zero
        Prims.nat
        Prims.nat
        (FStar.Seq.Base.length U_zero Pulse.Spec.GC.Base.hp_addr @x1)
        (FStar.Seq.Base.length
         U_zero
         Pulse.Spec.GC.Base.hp_addr
         x_a43c9a43db9e9f97f09b6905c39a534e_1)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
    :qid refinement_interpretation_Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
  :named refinement_interpretation_Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
; haseq for Tm_refine_4a81764065a4360e3f4d7b2c4beaa311
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
   (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr))))
  :named haseqTm_refine_4a81764065a4360e3f4d7b2c4beaa311))
(declare-fun Pulse.Spec.GC.GraphBridge.collect_all_edges (Term Term) Term)


; g: Pulse.Spec.GC.Base.heap ->     objs:       FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr         {FStar.Seq.Base.length objs << FStar.Seq.Base.length objs}   -> Prims.Ghost Pulse.Spec.GC.Graph.edge_list
(declare-fun Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3 () Term)
; kinding_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3
;;; Fact-ids: 
(assert
 (! (HasType Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3 (Tm_type U_zero))
  :named kinding_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40); use=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
    :qid Pulse.Spec.GC.GraphBridge_pre_typing_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
  :named Pulse.Spec.GC.GraphBridge_pre_typing_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
; interpretation_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40); use=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3)
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40); use=Pulse.Spec.GC.GraphBridge.fst(81,30-103,40)
      (forall ((@x1 Term) (@x2 Term))
       (! (implies
         (and
          ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39)
          (Valid
           ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39)
           (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x1))
          ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72)
          (Valid
           ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72)
           (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x1 @x2))
          (HasType @x1 Pulse.Spec.GC.Base.heap)
          (HasType @x2 Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
         (HasType (ApplyTT (ApplyTT @x0 @x1) @x2) Tm_refine_342151ed351c78dc8ce598768ff63d17))
        :pattern ((ApplyTT (ApplyTT @x0 @x1) @x2))
        :qid
         Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
    :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
  :named Pulse.Spec.GC.GraphBridge_interpretation_Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
(declare-fun Pulse.Spec.GC.GraphBridge.collect_all_edges@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25); use=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_all_edges@tok @x0) @x1)
     (Pulse.Spec.GC.GraphBridge.collect_all_edges @x0 @x1))
    :pattern ((ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_all_edges@tok @x0) @x1))
    :qid token_correspondence_Pulse.Spec.GC.GraphBridge.collect_all_edges))
  :named token_correspondence_Pulse.Spec.GC.GraphBridge.collect_all_edges))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25); use=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25)
  (forall ((@x0 Term))
   (! (and
     (NoHoist
      @x0
      (HasType
       Pulse.Spec.GC.GraphBridge.collect_all_edges@tok
       Tm_ghost_arrow_8c2da27ed71b2f6d3bc38779302ce5a3))
     ;; def=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25); use=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25)
     (forall ((@x1 Term) (@x2 Term))
      (! (=
        (ApplyTT (ApplyTT Pulse.Spec.GC.GraphBridge.collect_all_edges@tok @x1) @x2)
        (Pulse.Spec.GC.GraphBridge.collect_all_edges @x1 @x2))
       :pattern ((Pulse.Spec.GC.GraphBridge.collect_all_edges @x1 @x2))
       :qid function_token_typing_Pulse.Spec.GC.GraphBridge.collect_all_edges.1)))
    :pattern ((ApplyTT @x0 Pulse.Spec.GC.GraphBridge.collect_all_edges@tok))
    :qid function_token_typing_Pulse.Spec.GC.GraphBridge.collect_all_edges))
  :named function_token_typing_Pulse.Spec.GC.GraphBridge.collect_all_edges))

; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25); use=Pulse.Spec.GC.GraphBridge.fst(81,8-81,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39)
       (Pulse.Spec.GC.GraphBridge.all_objects_well_formed @x0))
      ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72)
      (Valid
       ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72)
       (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects @x0 @x1))
      (HasType @x0 Pulse.Spec.GC.Base.heap)
      (HasType @x1 Tm_refine_4a81764065a4360e3f4d7b2c4beaa311))
     (HasType
      (Pulse.Spec.GC.GraphBridge.collect_all_edges @x0 @x1)
      Tm_refine_342151ed351c78dc8ce598768ff63d17))
    :pattern ((Pulse.Spec.GC.GraphBridge.collect_all_edges @x0 @x1))
    :qid typing_Pulse.Spec.GC.GraphBridge.collect_all_edges))
  :named typing_Pulse.Spec.GC.GraphBridge.collect_all_edges))
(declare-fun label_26 () Bool)
(declare-fun label_25 () Bool)
(declare-fun label_24 () Bool)
(declare-fun label_23 () Bool)
(declare-fun label_22 () Bool)
(declare-fun label_21 () Bool)
(declare-fun label_20 () Bool)
(declare-fun label_19 () Bool)
(declare-fun label_18 () Bool)
(declare-fun label_17 () Bool)
(declare-fun label_16 () Bool)
(declare-fun label_15 () Bool)
(declare-fun label_14 () Bool)
(declare-fun label_13 () Bool)
(declare-fun label_12 () Bool)
(declare-fun label_11 () Bool)
(declare-fun label_10 () Bool)
(declare-fun label_9 () Bool)
(declare-fun label_8 () Bool)
(declare-fun label_7 () Bool)
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0 (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=FStar.Seq.Base.fsti(46,26-46,49); use=Pulse.Spec.GC.GraphBridge.fst(87,34-87,39)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0)
     (and
      (HasTypeFuel @u0 @x1 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.edge))
      ;; def=FStar.Seq.Base.fsti(46,37-46,47); use=Pulse.Spec.GC.GraphBridge.fst(87,34-87,39)
      (= (FStar.Seq.Base.length U_zero Pulse.Spec.GC.Graph.edge @x1) (BoxInt 0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
    :qid refinement_interpretation_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
  :named refinement_interpretation_Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
; haseq for Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
   (Valid (Prims.hasEq U_zero (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.edge))))
  :named haseqTm_refine_c5c708dce5ee6afb93df48bc8f455cf0))
; _: Pulse.Spec.GC.Base.hp_addr -> Prims.GTot Type0
(declare-fun Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c () Term)
; kinding_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c (Tm_type (U_succ U_zero)))
  :named kinding_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,47-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
    :qid Pulse.Spec.GC.GraphBridge_pre_typing_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
  :named Pulse.Spec.GC.GraphBridge_pre_typing_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
; interpretation_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(81,47-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c)
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(81,47-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
         (HasType (ApplyTT @x0 @x1) (Tm_type U_zero)))
        :pattern ((ApplyTT @x0 @x1))
        :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
    :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
  :named Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c))
(declare-fun Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b (Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-76,50); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x0) (Tm_type U_zero))
    :pattern ((HasType (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x0) (Tm_type U_zero)))
    :qid refinement_kinding_Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
  :named refinement_kinding_Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-76,50); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(637,71-637,97); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
      (not
       ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
       (forall ((@x3 Term))
        (! (implies
          (and
           (HasType @x3 Prims.unit)
           ;; def=Pulse.Spec.GC.GraphBridge.fst(76,10-76,50); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
           (implies
            ;; def=Pulse.Spec.GC.GraphBridge.fst(76,11-76,33); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (BoxBool_proj_0
             (FStar.Seq.Properties.mem
              Pulse.Spec.GC.Base.hp_addr
              @x2
              (FStar.Seq.Properties.tail
               U_zero
               Pulse.Spec.GC.Base.hp_addr
               x_a43c9a43db9e9f97f09b6905c39a534e_1)))
            ;; def=Pulse.Spec.GC.GraphBridge.fst(76,38-76,49); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (BoxBool_proj_0
             (FStar.Seq.Properties.mem
              Pulse.Spec.GC.Base.hp_addr
              @x2
              x_a43c9a43db9e9f97f09b6905c39a534e_1))))
          ;; def=Prims.fst(637,86-637,95); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
          (not
           ;; def=Prims.fst(637,86-637,95); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
           (= @x3 @x1)))
         :qid refinement_interpretation_Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b.1)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x2)))
    :qid refinement_interpretation_Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
  :named refinement_interpretation_Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
; haseq for Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-76,50); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq U_zero (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x0)))
     (Valid (Prims.hasEq U_zero Prims.unit)))
    :pattern ((Valid (Prims.hasEq U_zero (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x0))))
    :qid haseqTm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
  :named haseqTm_refine_bc2764d53dac8f57b6206e4bd6672e2b))
; x: Pulse.Spec.GC.Base.hp_addr   -> FStar.Pervasives.Lemma     (ensures       FStar.Seq.Properties.mem x (FStar.Seq.Properties.tail objs) ==>       FStar.Seq.Properties.mem x objs)
(declare-fun Tm_arrow_887539824376a20dbb4b47f159ed6152 () Term)
; kinding_Tm_arrow_887539824376a20dbb4b47f159ed6152
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_887539824376a20dbb4b47f159ed6152 (Tm_type U_zero))
  :named kinding_Tm_arrow_887539824376a20dbb4b47f159ed6152))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_887539824376a20dbb4b47f159ed6152)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_887539824376a20dbb4b47f159ed6152))
    :qid Pulse.Spec.GC.GraphBridge_pre_typing_Tm_arrow_887539824376a20dbb4b47f159ed6152))
  :named Pulse.Spec.GC.GraphBridge_pre_typing_Tm_arrow_887539824376a20dbb4b47f159ed6152))
; interpretation_Tm_arrow_887539824376a20dbb4b47f159ed6152
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_887539824376a20dbb4b47f159ed6152)
     (and
      ;; def=Pulse.Spec.GC.GraphBridge.fst(76,4-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Pulse.Spec.GC.Base.hp_addr)
         (HasType (ApplyTT @x0 @x1) (Tm_refine_bc2764d53dac8f57b6206e4bd6672e2b @x1)))
        :pattern ((ApplyTT @x0 @x1))
        :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_887539824376a20dbb4b47f159ed6152.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_887539824376a20dbb4b47f159ed6152))
    :qid Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_887539824376a20dbb4b47f159ed6152))
  :named Pulse.Spec.GC.GraphBridge_interpretation_Tm_arrow_887539824376a20dbb4b47f159ed6152))


(declare-fun Tm_abs_73b9128286c767d273451036b15bab18 () Term)
; typing_Tm_abs_73b9128286c767d273451036b15bab18
;;; Fact-ids: 
(assert
 (! (HasType Tm_abs_73b9128286c767d273451036b15bab18 Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c)
  :named typing_Tm_abs_73b9128286c767d273451036b15bab18))
; interpretation_Tm_abs_73b9128286c767d273451036b15bab18
;;; Fact-ids: 
(assert
 (! ;; def=Pulse.Spec.GC.GraphBridge.fst(76,10-76,50); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
  (forall ((@x0 Term))
   (! (=
     (ApplyTT Tm_abs_73b9128286c767d273451036b15bab18 @x0)
     (Prims.l_imp
      (Prims.b2t
       (FStar.Seq.Properties.mem
        Pulse.Spec.GC.Base.hp_addr
        @x0
        (FStar.Seq.Properties.tail
         U_zero
         Pulse.Spec.GC.Base.hp_addr
         x_a43c9a43db9e9f97f09b6905c39a534e_1)))
      (Prims.b2t
       (FStar.Seq.Properties.mem Pulse.Spec.GC.Base.hp_addr @x0 x_a43c9a43db9e9f97f09b6905c39a534e_1))))
    :pattern ((ApplyTT Tm_abs_73b9128286c767d273451036b15bab18 @x0))
    :qid interpretation_Tm_abs_73b9128286c767d273451036b15bab18))
  :named interpretation_Tm_abs_73b9128286c767d273451036b15bab18))
; Encoding query formula : (forall (p: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;     Pulse.Spec.GC.GraphBridge.all_objects_well_formed g /\
;     Pulse.Spec.GC.GraphBridge.objs_subset_of_objects g objs /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list). Prims.auto_squash (p ghost_result)) ==>
;     (forall (k: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;         (forall (x: Pulse.Spec.GC.Graph.edge_list). {:pattern Prims.guard_free (k x)}
;             (x ==
;               (match FStar.Seq.Base.length objs = 0 with
;                 | true -> seq![]
;                 | _ ->
;                   FStar.Seq.Base.append (Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                         (FStar.Seq.Properties.head objs)
;                         (Pulse.Spec.GC.Object.wosize_of_object (FStar.Seq.Properties.head objs) g)
;                         (0uL <: FStar.UInt64.t))
;                     (Pulse.Spec.GC.GraphBridge.collect_all_edges g (FStar.Seq.Properties.tail objs))
;               ) ==>
;               (forall (return_val: Pulse.Spec.GC.Graph.edge_list). return_val == x ==> p return_val)
;             ) ==>
;             k x) ==>
;         (FStar.Seq.Base.length objs = 0 == true ==>
;           (forall (return_val:
;               s: FStar.Seq.Base.seq Pulse.Spec.GC.Graph.edge {FStar.Seq.Base.length s = 0}).
;               return_val == seq![] ==> k return_val)) /\
;         (~(FStar.Seq.Base.length objs = 0 = true) ==>
;           (forall (b: Prims.bool).
;               FStar.Seq.Base.length objs = 0 == b ==>
;               FStar.Seq.Base.length objs > 0 /\
;               (forall (any_result: FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr).
;                   objs == any_result ==>
;                   (forall (any_result: Pulse.Spec.GC.Base.hp_addr).
;                       FStar.Seq.Properties.head objs == any_result ==>
;                       Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;                       (forall (any_result: Type0).
;                           Pulse.Spec.GC.Base.hp_addr == any_result ==>
;                           FStar.Seq.Base.length objs > 0 /\
;                           (forall (any_result: FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr).
;                               objs == any_result ==>
;                               (forall (pure_result: Prims.unit).
;                                   FStar.Seq.Properties.mem (FStar.Seq.Properties.head objs) objs ==>
;                                   Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;                                   (forall (any_result: Type0).
;                                       Pulse.Spec.GC.Base.hp_addr == any_result ==>
;                                       (forall (any_result: Prims.bool).
;                                           FStar.Seq.Properties.mem (FStar.Seq.Properties.head objs)
;                                             objs ==
;                                           any_result ==>
;                                           (forall (any_result: Prims.logical).
;                                               FStar.Seq.Properties.mem (FStar.Seq.Properties.head objs
;                                                   )
;                                                 objs ==
;                                               any_result ==>
;                                               FStar.Seq.Properties.mem (FStar.Seq.Properties.head objs
;                                                   )
;                                                 objs /\
;                                               (forall (pure_result: Prims.unit).
;                                                   FStar.Seq.Properties.mem (FStar.Seq.Properties.head
;                                                         objs)
;                                                     objs ==>
;                                                   Prims.hasEq Pulse.Spec.GC.Base.hp_addr /\
;                                                   (forall (any_result: Type0).
;                                                       Pulse.Spec.GC.Base.hp_addr == any_result ==>
;                                                       0 < Pulse.Spec.GC.Base.heap_size /\
;                                                       0 % FStar.UInt64.v Pulse.Spec.GC.Base.mword ==
;                                                       0 /\
;                                                       (forall (return_val:
;                                                           Pulse.Spec.GC.Base.hp_addr).
;                                                           return_val == 0uL ==>
;                                                           (forall (any_result:
;                                                               FStar.Seq.Base.seq Pulse.Spec.GC.Base.hp_addr
;                                                               ).
;                                                               Pulse.Spec.GC.Fields.objects (0uL
;                                                                   <:
;                                                                   FStar.UInt64.t)
;                                                                 g ==
;                                                               any_result ==>
;                                                               (forall (any_result: Prims.bool).
;                                                                   FStar.Seq.Properties.mem (FStar.Seq.Properties.head
;                                                                         objs)
;                                                                     (Pulse.Spec.GC.Fields.objects (0uL
;                                                                           <:
;                                                                           FStar.UInt64.t)
;                                                                         g) ==
;                                                                   any_result ==>
;                                                                   (forall (any_result:
;                                                                       Prims.logical).
;                                                                       FStar.Seq.Properties.mem (FStar.Seq.Properties.head
;                                                                             objs)
;                                                                         (Pulse.Spec.GC.Fields.objects
;                                                                             (0uL <: FStar.UInt64.t)
;                                                                             g) ==
;                                                                       any_result ==>
;                                                                       FStar.Seq.Properties.mem (FStar.Seq.Properties.head
;                                                                             objs)
;                                                                         (Pulse.Spec.GC.Fields.objects
;                                                                             (0uL <: FStar.UInt64.t)
;                                                                             g) /\
;                                                                       (forall (pure_result:
;                                                                           Prims.unit).
;                                                                           FStar.Seq.Properties.mem (FStar.Seq.Properties.head
;                                                                                 objs)
;                                                                             (Pulse.Spec.GC.Fields.objects
;                                                                                 (0uL
;                                                                                   <:
;                                                                                   FStar.UInt64.t)
;                                                                                 g) ==>
;                                                                           Pulse.Spec.GC.Fields.well_formed_object
;                                                                             g
;                                                                             (FStar.Seq.Properties.head
;                                                                                 objs) /\
;                                                                           (forall (pure_result:
;                                                                               Prims.unit).
;                                                                               Pulse.Spec.GC.Fields.well_formed_object
;                                                                                 g
;                                                                                 (FStar.Seq.Properties.head
;                                                                                     objs) ==>
;                                                                               (forall (pure_result:
;                                                                                   Prims.unit).
;                                                                                   FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object
;                                                                                         (FStar.Seq.Properties.head
;                                                                                             objs)
;                                                                                         g) <
;                                                                                   Prims.pow2 54 ==>
;                                                                                   FStar.UInt64.v (Pulse.Spec.GC.Object.wosize_of_object
;                                                                                         (FStar.Seq.Properties.head
;                                                                                             objs)
;                                                                                         g) <
;                                                                                   Prims.pow2 54 /\
;                                                                                   (forall (any_result:
;                                                                                       FStar.UInt64.t)
;                                                                                     .
;                                                                                       Pulse.Spec.GC.Object.wosize_of_object
;                                                                                         (FStar.Seq.Properties.head
;                                                                                             objs)
;                                                                                         g ==
;                                                                                       any_result ==>
;                                                                                       Pulse.Spec.GC.Fields.well_formed_object
;                                                                                         g
;                                                                                         (FStar.Seq.Properties.head
;                                                                                             objs) /\
;                                                                                       FStar.UInt64.v
;                                                                                         (Pulse.Spec.GC.Object.wosize_of_object
;                                                                                             (FStar.Seq.Properties.head
;                                                                                                 objs
;                                                                                             )
;                                                                                             g) <=
;                                                                                       FStar.UInt64.v
;                                                                                         (Pulse.Spec.GC.Object.wosize_of_object
;                                                                                             (FStar.Seq.Properties.head
;                                                                                                 objs
;                                                                                             )
;                                                                                             g) /\
;                                                                                       (forall (ghost_result:
;                                                                                           Pulse.Spec.GC.Graph.edge_list)
;                                                                                         .
;                                                                                           Pulse.Spec.GC.GraphBridge.collect_edges_from_object
;                                                                                             g
;                                                                                             (FStar.Seq.Properties.head
;                                                                                                 objs
;                                                                                             )
;                                                                                             (Pulse.Spec.GC.Object.wosize_of_object
;                                                                                                 (FStar.Seq.Properties.head
;                                                                                                     objs
;                                                                                                   )
;                                                                                                 g)
;                                                                                             (0uL
;                                                                                               <:
;                                                                                               FStar.UInt64.t
;                                                                                             ) ==
;                                                                                           ghost_result ==>
;                                                                                           (forall (x:
;                                                                                               Pulse.Spec.GC.Base.hp_addr)
;                                                                                             .
;                                                                                               (* - Could not prove post-condition *)
;                                                                                               Prims.hasEq
;                                                                                                 Pulse.Spec.GC.Base.hp_addr
;                                                                                                /\
;                                                                                               (forall
;                                                                                                   (any_result:
;                                                                                                   Type0)
;                                                                                                 .
;                                                                                                   Pulse.Spec.GC.Base.hp_addr ==
;                                                                                                   any_result ==>
;                                                                                                   FStar.Seq.Base.length
;                                                                                                     objs
;                                                                                                    >
;                                                                                                   0) /\
;                                                                                               (FStar.Seq.Properties.mem
;                                                                                                   x
;                                                                                                   (FStar.Seq.Properties.tail
;                                                                                                       objs
; 
;                                                                                                   ) ==>
;                                                                                                 Prims.hasEq
;                                                                                                   Pulse.Spec.GC.Base.hp_addr
;                                                                                                 )) /\
;                                                                                           (forall (any_result:
;                                                                                               (
;                                                                                                     _:
;                                                                                                       Pulse.Spec.GC.Base.hp_addr
;                                                                                                   -> Prims.GTot
;                                                                                                     Type0
;                                                                                               )).
;                                                                                               (fun
;                                                                                                   x
;                                                                                                   ->
;                                                                                                   FStar.Seq.Properties.mem
;                                                                                                     x
;                                                                                                     (
;                                                                                                       FStar.Seq.Properties.tail
;                                                                                                         objs
; 
;                                                                                                     )
;                                                                                                    ==>
;                                                                                                   FStar.Seq.Properties.mem
;                                                                                                     x
;                                                                                                     objs
;                                                                                                   ) ==
;                                                                                               any_result ==>
;                                                                                               Prims.hasEq
;                                                                                                 Pulse.Spec.GC.Base.hp_addr
;                                                                                                /\
;                                                                                               (forall
;                                                                                                   (any_result:
;                                                                                                   Type0)
;                                                                                                 .
;                                                                                                   Pulse.Spec.GC.Base.hp_addr ==
;                                                                                                   any_result ==>
;                                                                                                   FStar.Seq.Base.length
;                                                                                                     objs
;                                                                                                    >
;                                                                                                   0 /\
;                                                                                                   (forall
;                                                                                                       (any_result:
;                                                                                                       FStar.Seq.Base.seq
;                                                                                                         Pulse.Spec.GC.Base.hp_addr
;                                                                                                       )
;                                                                                                     .
;                                                                                                       objs ==
;                                                                                                       any_result ==>
;                                                                                                       (
;                                                                                                         forall
;                                                                                                           (any_result:
;                                                                                                           (
; 
;                                                                                                                 x:
;                                                                                                                   Pulse.Spec.GC.Base.hp_addr
;                                                                                                               -> FStar.Pervasives.Lemma
;                                                                                                                 (
;                                                                                                                   ensures
;                                                                                                                   FStar.Seq.Properties.mem
;                                                                                                                     x
;                                                                                                                     (
;                                                                                                                       FStar.Seq.Properties.tail
;                                                                                                                         objs
; 
;                                                                                                                     )
;                                                                                                                    ==>
;                                                                                                                   FStar.Seq.Properties.mem
;                                                                                                                     x
;                                                                                                                     objs
; 
;                                                                                                                 )
;                                                                                                           ))
;                                                                                                           (pure_result:
;                                                                                                           Prims.unit)
;                                                                                                         .
;                                                                                                           (
;                                                                                                             forall
;                                                                                                               (x:
;                                                                                                               Pulse.Spec.GC.Base.hp_addr)
;                                                                                                             .
;                                                                                                               FStar.Seq.Properties.mem
;                                                                                                                 x
;                                                                                                                 (
;                                                                                                                   FStar.Seq.Properties.tail
;                                                                                                                     objs
; 
;                                                                                                                 )
;                                                                                                                ==>
;                                                                                                               FStar.Seq.Properties.mem
;                                                                                                                 x
;                                                                                                                 objs
; 
;                                                                                                           ) ==>
;                                                                                                           FStar.Seq.Base.length
;                                                                                                             objs
;                                                                                                            >
;                                                                                                           0 /\
;                                                                                                           (
;                                                                                                             forall
;                                                                                                               (any_result:
;                                                                                                               FStar.Seq.Base.seq
;                                                                                                                 Pulse.Spec.GC.Base.hp_addr
;                                                                                                               )
;                                                                                                             .
;                                                                                                               objs ==
;                                                                                                               any_result ==>
;                                                                                                               (
;                                                                                                                 forall
;                                                                                                                   (any_result:
;                                                                                                                   FStar.Seq.Base.seq
;                                                                                                                     Pulse.Spec.GC.Base.hp_addr
;                                                                                                                   )
;                                                                                                                 .
;                                                                                                                   FStar.Seq.Properties.tail
;                                                                                                                     objs
;                                                                                                                    ==
;                                                                                                                   any_result ==>
;                                                                                                                   FStar.Seq.Base.length
;                                                                                                                     (
;                                                                                                                       FStar.Seq.Properties.tail
;                                                                                                                         objs
; 
;                                                                                                                     )
;                                                                                                                    <<
;                                                                                                                   FStar.Seq.Base.length
;                                                                                                                     objs
;                                                                                                                    /\
;                                                                                                                   (
;                                                                                                                     forall
;                                                                                                                       (return_val:
;                                                                                                                       objs:
;                                                                                                                       FStar.Seq.Base.seq
;                                                                                                                         Pulse.Spec.GC.Base.hp_addr
; 
;                                                                                                                         {
;                                                                                                                           FStar.Seq.Base.length
;                                                                                                                             objs
;                                                                                                                            <<
;                                                                                                                           FStar.Seq.Base.length
;                                                                                                                             objs
; 
;                                                                                                                         })
;                                                                                                                     .
;                                                                                                                       return_val ==
;                                                                                                                       FStar.Seq.Properties.tail
;                                                                                                                         objs
;                                                                                                                        ==>
;                                                                                                                       FStar.Seq.Properties.tail
;                                                                                                                         objs
;                                                                                                                        ==
;                                                                                                                       return_val ==>
;                                                                                                                       Pulse.Spec.GC.GraphBridge.all_objects_well_formed
;                                                                                                                         g
;                                                                                                                        /\
;                                                                                                                       Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
;                                                                                                                         g
;                                                                                                                         (
;                                                                                                                           FStar.Seq.Properties.tail
;                                                                                                                             objs
; 
;                                                                                                                         )
;                                                                                                                        /\
;                                                                                                                       (
;                                                                                                                         forall
;                                                                                                                           (ghost_result:
;                                                                                                                           Pulse.Spec.GC.Graph.edge_list)
;                                                                                                                         .
;                                                                                                                           Pulse.Spec.GC.GraphBridge.collect_all_edges
;                                                                                                                             g
;                                                                                                                             (
;                                                                                                                               FStar.Seq.Properties.tail
;                                                                                                                                 objs
; 
;                                                                                                                             )
;                                                                                                                            ==
;                                                                                                                           ghost_result ==>
;                                                                                                                           (
;                                                                                                                             forall
;                                                                                                                               (any_result:
;                                                                                                                               Pulse.Spec.GC.Graph.edge_list)
;                                                                                                                             .
;                                                                                                                               k
;                                                                                                                                 any_result
; 
;                                                                                                                           )
;                                                                                                                       )
;                                                                                                                   )
;                                                                                                               )
;                                                                                                           )
;                                                                                                       )
;                                                                                                   ))
;                                                                                           ))))))))))
;                                                   )))))))))))))) /\
; (forall (p: Prims.pure_post Pulse.Spec.GC.Graph.edge_list).
;     Pulse.Spec.GC.GraphBridge.all_objects_well_formed g /\
;     Pulse.Spec.GC.GraphBridge.objs_subset_of_objects g objs /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list). Prims.auto_squash (p ghost_result)) ==>
;     Pulse.Spec.GC.GraphBridge.all_objects_well_formed g /\
;     Pulse.Spec.GC.GraphBridge.objs_subset_of_objects g objs /\
;     (forall (ghost_result: Pulse.Spec.GC.Graph.edge_list).
;         ghost_result ==
;         (match FStar.Seq.Base.length objs = 0 with
;           | true -> seq![]
;           | _ ->
;             FStar.Seq.Base.append (Pulse.Spec.GC.GraphBridge.collect_edges_from_object g
;                   (FStar.Seq.Properties.head objs)
;                   (Pulse.Spec.GC.Object.wosize_of_object (FStar.Seq.Properties.head objs) g)
;                   (0uL <: FStar.UInt64.t))
;               (Pulse.Spec.GC.GraphBridge.collect_all_edges g (FStar.Seq.Properties.tail objs))) ==>
;         (forall (return_val: Pulse.Spec.GC.Graph.edge_list).
;             return_val == ghost_result ==> p return_val)))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec collect_all_edges`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=Prims.fst(414,51-414,91); use=Prims.fst(438,19-438,32)
   (and
    ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
    (forall ((@x0 Term))
     (! (implies
       (and
        (HasType @x0 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Pulse.Spec.GC.GraphBridge.all_objects_well_formed x_e246fc25c9201731c203dc9e18738560_0))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
          x_e246fc25c9201731c203dc9e18738560_0
          x_a43c9a43db9e9f97f09b6905c39a534e_1))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (forall ((@x1 Term))
         (! (implies
           (or label_1 (HasType @x1 Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
           (Valid
            ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (ApplyTT @x0 @x1)))
          :pattern
           (;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (Valid
             ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
             (ApplyTT @x0 @x1)))
          :qid @query.1)))
       ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
       (forall ((@x1 Term))
        (! (implies
          (and
           (HasType @x1 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
           (forall ((@x2 Term))
            (! (implies
              (implies
               ;; def=Pulse.Spec.GC.GraphBridge.fst(82,10-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
               (=
                @x2
                (let
                  ((@lb3
                    (Prims.op_Equality
                     Prims.int
                     (FStar.Seq.Base.length
                      U_zero
                      Pulse.Spec.GC.Base.hp_addr
                      x_a43c9a43db9e9f97f09b6905c39a534e_1)
                     (BoxInt 0))))
                 (ite
                  (= @lb3 (BoxBool true))
                  (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)
                  (FStar.Seq.Base.append
                   U_zero
                   Pulse.Spec.GC.Graph.edge
                   (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                    x_e246fc25c9201731c203dc9e18738560_0
                    (FStar.Seq.Properties.head
                     U_zero
                     Pulse.Spec.GC.Base.hp_addr
                     x_a43c9a43db9e9f97f09b6905c39a534e_1)
                    (Pulse.Spec.GC.Object.wosize_of_object
                     (FStar.Seq.Properties.head
                      U_zero
                      Pulse.Spec.GC.Base.hp_addr
                      x_a43c9a43db9e9f97f09b6905c39a534e_1)
                     x_e246fc25c9201731c203dc9e18738560_0)
                    (FStar.UInt64.uint_to_t (BoxInt 0)))
                   (Pulse.Spec.GC.GraphBridge.collect_all_edges
                    x_e246fc25c9201731c203dc9e18738560_0
                    (FStar.Seq.Properties.tail
                     U_zero
                     Pulse.Spec.GC.Base.hp_addr
                     x_a43c9a43db9e9f97f09b6905c39a534e_1))))))
               ;; def=Prims.fst(364,2-364,58); use=Prims.fst(434,19-434,31)
               (forall ((@x3 Term))
                (! (implies
                  (and
                   (HasType @x3 Pulse.Spec.GC.Graph.edge_list)
                   ;; def=Prims.fst(364,26-364,41); use=Prims.fst(434,19-434,31)
                   (= @x3 @x2))
                  ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
                  (Valid
                   ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
                   (ApplyTT @x0 @x3)))
                 :qid @query.4)))
              ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
              (Valid
               ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
               (ApplyTT @x1 @x2)))
             :weight 0
             :pattern ((ApplyTT @x1 @x2))
             :qid @query.3)))
          ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
          (and
           (implies
            ;; def=Pulse.Spec.GC.GraphBridge.fst(87,5-87,24); use=Pulse.Spec.GC.GraphBridge.fst(87,5-87,24)
            (=
             (Prims.op_Equality
              Prims.int
              (FStar.Seq.Base.length
               U_zero
               Pulse.Spec.GC.Base.hp_addr
               x_a43c9a43db9e9f97f09b6905c39a534e_1)
              (BoxInt 0))
             (BoxBool true))
            ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (forall ((@x2 Term))
             (! (implies
               (and
                (HasType @x2 Tm_refine_c5c708dce5ee6afb93df48bc8f455cf0)
                ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                (= @x2 (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)))
               ;; def=Prims.fst(364,46-364,58); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
               (Valid
                ;; def=Prims.fst(364,46-364,58); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                (ApplyTT @x1 @x2)))
              :qid @query.5)))
           (implies
            ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (not
             ;; def=Pulse.Spec.GC.GraphBridge.fst(87,5-87,24); use=Pulse.Spec.GC.GraphBridge.fst(87,5-87,24)
             (=
              (Prims.op_Equality
               Prims.int
               (FStar.Seq.Base.length
                U_zero
                Pulse.Spec.GC.Base.hp_addr
                x_a43c9a43db9e9f97f09b6905c39a534e_1)
               (BoxInt 0))
              (BoxBool true)))
            ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (forall ((@x2 Term))
             (! (implies
               (and
                (HasType @x2 Prims.bool)
                ;; def=Pulse.Spec.GC.GraphBridge.fst(87,5-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,5-103,40)
                (=
                 (Prims.op_Equality
                  Prims.int
                  (FStar.Seq.Base.length
                   U_zero
                   Pulse.Spec.GC.Base.hp_addr
                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                  (BoxInt 0))
                 @x2))
               ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
               (and
                ;; def=FStar.Seq.Properties.fsti(40,28-40,40); use=Pulse.Spec.GC.GraphBridge.fst(89,23-89,27)
                (or
                 label_2
                 ;; def=FStar.Seq.Properties.fsti(40,28-40,40); use=Pulse.Spec.GC.GraphBridge.fst(89,23-89,27)
                 (>
                  (BoxInt_proj_0
                   (FStar.Seq.Base.length
                    U_zero
                    Pulse.Spec.GC.Base.hp_addr
                    x_a43c9a43db9e9f97f09b6905c39a534e_1))
                  (BoxInt_proj_0 (BoxInt 0))))
                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                (forall ((@x3 Term))
                 (! (implies
                   (and
                    (HasType @x3 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr))
                    ;; def=FStar.Seq.Properties.fsti(40,20-40,21); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                    (= x_a43c9a43db9e9f97f09b6905c39a534e_1 @x3))
                   ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                   (forall ((@x4 Term))
                    (! (implies
                      (and
                       (HasType @x4 Pulse.Spec.GC.Base.hp_addr)
                       ;; def=Pulse.Spec.GC.GraphBridge.fst(89,8-89,27); use=Pulse.Spec.GC.GraphBridge.fst(89,8-89,27)
                       (=
                        (FStar.Seq.Properties.head
                         U_zero
                         Pulse.Spec.GC.Base.hp_addr
                         x_a43c9a43db9e9f97f09b6905c39a534e_1)
                        @x4))
                      ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                      (and
                       ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(90,19-90,23)
                       (or
                        label_3
                        ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(90,19-90,23)
                        (Valid
                         ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(90,19-90,23)
                         (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
                       ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                       (forall ((@x5 Term))
                        (! (implies
                          (and
                           (HasType @x5 (Tm_type U_zero))
                           ;; def=Pulse.Spec.GC.GraphBridge.fst(68,21-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                           (= Pulse.Spec.GC.Base.hp_addr @x5))
                          ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                          (and
                           ;; def=Pulse.Spec.GC.GraphBridge.fst(68,42-68,58); use=Pulse.Spec.GC.GraphBridge.fst(90,19-90,23)
                           (or
                            label_4
                            ;; def=Pulse.Spec.GC.GraphBridge.fst(68,42-68,58); use=Pulse.Spec.GC.GraphBridge.fst(90,19-90,23)
                            (>
                             (BoxInt_proj_0
                              (FStar.Seq.Base.length
                               U_zero
                               Pulse.Spec.GC.Base.hp_addr
                               x_a43c9a43db9e9f97f09b6905c39a534e_1))
                             (BoxInt_proj_0 (BoxInt 0))))
                           ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                           (forall ((@x6 Term))
                            (! (implies
                              (and
                               (HasType @x6 (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Base.hp_addr))
                               ;; def=Pulse.Spec.GC.GraphBridge.fst(68,33-81,41); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                               (= x_a43c9a43db9e9f97f09b6905c39a534e_1 @x6))
                              ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(90,4-90,18)
                              (forall ((@x7 Term))
                               (! (implies
                                 (and
                                  (HasType @x7 Prims.unit)
                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(69,10-69,34); use=Pulse.Spec.GC.GraphBridge.fst(90,4-90,18)
                                  (BoxBool_proj_0
                                   (FStar.Seq.Properties.mem
                                    Pulse.Spec.GC.Base.hp_addr
                                    (FStar.Seq.Properties.head
                                     U_zero
                                     Pulse.Spec.GC.Base.hp_addr
                                     x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                    x_a43c9a43db9e9f97f09b6905c39a534e_1)))
                                 ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                 (and
                                  ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(92,24-92,28)
                                  (or
                                   label_5
                                   ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(92,24-92,28)
                                   (Valid
                                    ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(92,24-92,28)
                                    (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
                                  ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                  (forall ((@x8 Term))
                                   (! (implies
                                     (and
                                      (HasType @x8 (Tm_type U_zero))
                                      ;; def=FStar.Seq.Properties.fsti(77,10-77,11); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                      (= Pulse.Spec.GC.Base.hp_addr @x8))
                                     ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                     (forall ((@x9 Term))
                                      (! (implies
                                        (and
                                         (HasType @x9 Prims.bool)
                                         ;; def=Prims.fst(188,10-188,11); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                         (=
                                          (FStar.Seq.Properties.mem
                                           Pulse.Spec.GC.Base.hp_addr
                                           (FStar.Seq.Properties.head
                                            U_zero
                                            Pulse.Spec.GC.Base.hp_addr
                                            x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                           x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                          @x9))
                                        ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                        (forall ((@x10 Term))
                                         (! (implies
                                           (and
                                            (HasType @x10 Prims.logical)
                                            ;; def=Prims.fst(674,13-674,14); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                            (=
                                             (Prims.b2t
                                              (FStar.Seq.Properties.mem
                                               Pulse.Spec.GC.Base.hp_addr
                                               (FStar.Seq.Properties.head
                                                U_zero
                                                Pulse.Spec.GC.Base.hp_addr
                                                x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                               x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                             @x10))
                                           ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(92,4-92,10)
                                           (and
                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(92,11-92,29); use=Pulse.Spec.GC.GraphBridge.fst(92,4-92,10)
                                            (or
                                             label_6
                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(92,11-92,29); use=Pulse.Spec.GC.GraphBridge.fst(92,4-92,10)
                                             (BoxBool_proj_0
                                              (FStar.Seq.Properties.mem
                                               Pulse.Spec.GC.Base.hp_addr
                                               (FStar.Seq.Properties.head
                                                U_zero
                                                Pulse.Spec.GC.Base.hp_addr
                                                x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                               x_a43c9a43db9e9f97f09b6905c39a534e_1)))
                                            ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(92,4-92,10)
                                            (forall ((@x11 Term))
                                             (! (implies
                                               (and
                                                (HasType @x11 Prims.unit)
                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(92,11-92,29); use=Pulse.Spec.GC.GraphBridge.fst(92,4-92,10)
                                                (BoxBool_proj_0
                                                 (FStar.Seq.Properties.mem
                                                  Pulse.Spec.GC.Base.hp_addr
                                                  (FStar.Seq.Properties.head
                                                   U_zero
                                                   Pulse.Spec.GC.Base.hp_addr
                                                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                  x_a43c9a43db9e9f97f09b6905c39a534e_1)))
                                               ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                               (and
                                                ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(93,25-93,32)
                                                (or
                                                 label_7
                                                 ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(93,25-93,32)
                                                 (Valid
                                                  ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(93,25-93,32)
                                                  (Prims.hasEq U_zero Pulse.Spec.GC.Base.hp_addr)))
                                                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                (forall ((@x12 Term))
                                                 (! (implies
                                                   (and
                                                    (HasType @x12 (Tm_type U_zero))
                                                    ;; def=FStar.Seq.Properties.fsti(77,10-77,11); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                    (= Pulse.Spec.GC.Base.hp_addr @x12))
                                                   ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                   (and
                                                    ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(93,33-93,36)
                                                    (or
                                                     label_8
                                                     ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(93,33-93,36)
                                                     (<
                                                      (BoxInt_proj_0 (BoxInt 0))
                                                      (BoxInt_proj_0
                                                       (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                                    ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(93,33-93,36)
                                                    (or
                                                     label_9
                                                     ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(93,33-93,36)
                                                     (=
                                                      (Prims.op_Modulus
                                                       (BoxInt 0)
                                                       (FStar.UInt64.v
                                                        (Pulse.Spec.GC.Base.mword Dummy_value)))
                                                      (BoxInt 0)))
                                                    ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                    (forall ((@x13 Term))
                                                     (! (implies
                                                       (and
                                                        (HasType @x13 Pulse.Spec.GC.Base.hp_addr)
                                                        ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                        (= @x13 (FStar.UInt64.uint_to_t (BoxInt 0))))
                                                       ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                       (forall ((@x14 Term))
                                                        (! (implies
                                                          (and
                                                           (HasType
                                                            @x14
                                                            (FStar.Seq.Base.seq
                                                             U_zero
                                                             Pulse.Spec.GC.Base.hp_addr))
                                                           ;; def=FStar.Seq.Properties.fsti(77,27-77,28); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                           (=
                                                            (Pulse.Spec.GC.Fields.objects
                                                             (FStar.UInt64.uint_to_t (BoxInt 0))
                                                             x_e246fc25c9201731c203dc9e18738560_0)
                                                            @x14))
                                                          ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                          (forall ((@x15 Term))
                                                           (! (implies
                                                             (and
                                                              (HasType @x15 Prims.bool)
                                                              ;; def=Prims.fst(188,10-188,11); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                              (=
                                                               (FStar.Seq.Properties.mem
                                                                Pulse.Spec.GC.Base.hp_addr
                                                                (FStar.Seq.Properties.head
                                                                 U_zero
                                                                 Pulse.Spec.GC.Base.hp_addr
                                                                 x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                (Pulse.Spec.GC.Fields.objects
                                                                 (FStar.UInt64.uint_to_t (BoxInt 0))
                                                                 x_e246fc25c9201731c203dc9e18738560_0))
                                                               @x15))
                                                             ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                             (forall ((@x16 Term))
                                                              (! (implies
                                                                (and
                                                                 (HasType @x16 Prims.logical)
                                                                 ;; def=Prims.fst(674,13-674,14); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                 (=
                                                                  (Prims.b2t
                                                                   (FStar.Seq.Properties.mem
                                                                    Pulse.Spec.GC.Base.hp_addr
                                                                    (FStar.Seq.Properties.head
                                                                     U_zero
                                                                     Pulse.Spec.GC.Base.hp_addr
                                                                     x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                    (Pulse.Spec.GC.Fields.objects
                                                                     (FStar.UInt64.uint_to_t
                                                                      (BoxInt 0))
                                                                     x_e246fc25c9201731c203dc9e18738560_0)))
                                                                  @x16))
                                                                ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(93,4-93,10)
                                                                (and
                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(93,11-93,40); use=Pulse.Spec.GC.GraphBridge.fst(93,4-93,10)
                                                                 (or
                                                                  label_10
                                                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(93,11-93,40); use=Pulse.Spec.GC.GraphBridge.fst(93,4-93,10)
                                                                  (BoxBool_proj_0
                                                                   (FStar.Seq.Properties.mem
                                                                    Pulse.Spec.GC.Base.hp_addr
                                                                    (FStar.Seq.Properties.head
                                                                     U_zero
                                                                     Pulse.Spec.GC.Base.hp_addr
                                                                     x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                    (Pulse.Spec.GC.Fields.objects
                                                                     (FStar.UInt64.uint_to_t
                                                                      (BoxInt 0))
                                                                     x_e246fc25c9201731c203dc9e18738560_0))))
                                                                 ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(93,4-93,10)
                                                                 (forall ((@x17 Term))
                                                                  (! (implies
                                                                    (and
                                                                     (HasType @x17 Prims.unit)
                                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(93,11-93,40); use=Pulse.Spec.GC.GraphBridge.fst(93,4-93,10)
                                                                     (BoxBool_proj_0
                                                                      (FStar.Seq.Properties.mem
                                                                       Pulse.Spec.GC.Base.hp_addr
                                                                       (FStar.Seq.Properties.head
                                                                        U_zero
                                                                        Pulse.Spec.GC.Base.hp_addr
                                                                        x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                       (Pulse.Spec.GC.Fields.objects
                                                                        (FStar.UInt64.uint_to_t
                                                                         (BoxInt 0))
                                                                        x_e246fc25c9201731c203dc9e18738560_0))))
                                                                    ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                    (and
                                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(95,11-95,37); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                     (or
                                                                      label_11
                                                                      ;; def=Pulse.Spec.GC.GraphBridge.fst(95,11-95,37); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                      (Valid
                                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(95,11-95,37); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                       (Pulse.Spec.GC.Fields.well_formed_object
                                                                        x_e246fc25c9201731c203dc9e18738560_0
                                                                        (FStar.Seq.Properties.head
                                                                         U_zero
                                                                         Pulse.Spec.GC.Base.hp_addr
                                                                         x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                     ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                     (forall ((@x18 Term))
                                                                      (! (implies
                                                                        (and
                                                                         (HasType @x18 Prims.unit)
                                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(95,11-95,37); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                         (Valid
                                                                          ;; def=Pulse.Spec.GC.GraphBridge.fst(95,11-95,37); use=Pulse.Spec.GC.GraphBridge.fst(95,4-95,10)
                                                                          (Pulse.Spec.GC.Fields.well_formed_object
                                                                           x_e246fc25c9201731c203dc9e18738560_0
                                                                           (FStar.Seq.Properties.head
                                                                            U_zero
                                                                            Pulse.Spec.GC.Base.hp_addr
                                                                            x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                        ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(97,4-97,26)
                                                                        (forall ((@x19 Term))
                                                                         (! (implies
                                                                           (and
                                                                            (HasType @x19 Prims.unit)
                                                                            ;; def=Pulse.Spec.GC.Object.fsti(110,8-110,53); use=Pulse.Spec.GC.GraphBridge.fst(97,4-97,26)
                                                                            (<
                                                                             (BoxInt_proj_0
                                                                              (FStar.UInt64.v
                                                                               (Pulse.Spec.GC.Object.wosize_of_object
                                                                                (FStar.Seq.Properties.head
                                                                                 U_zero
                                                                                 Pulse.Spec.GC.Base.hp_addr
                                                                                 x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                x_e246fc25c9201731c203dc9e18738560_0)))
                                                                             (BoxInt_proj_0
                                                                              (Prims.pow2
                                                                               (BoxInt 54)))))
                                                                           ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                           (and
                                                                            ;; def=Pulse.Spec.GC.Fields.fst(25,22-25,39); use=Pulse.Spec.GC.GraphBridge.fst(98,22-98,28)
                                                                            (or
                                                                             label_12
                                                                             ;; def=Pulse.Spec.GC.Fields.fst(25,22-25,39); use=Pulse.Spec.GC.GraphBridge.fst(98,22-98,28)
                                                                             (<
                                                                              (BoxInt_proj_0
                                                                               (FStar.UInt64.v
                                                                                (Pulse.Spec.GC.Object.wosize_of_object
                                                                                 (FStar.Seq.Properties.head
                                                                                  U_zero
                                                                                  Pulse.Spec.GC.Base.hp_addr
                                                                                  x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                 x_e246fc25c9201731c203dc9e18738560_0)))
                                                                              (BoxInt_proj_0
                                                                               (Prims.pow2
                                                                                (BoxInt 54)))))
                                                                            ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                            (forall ((@x20 Term))
                                                                             (! (implies
                                                                               (and
                                                                                (HasType
                                                                                 @x20
                                                                                 (FStar.UInt64.t
                                                                                  Dummy_value))
                                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(96,8-98,10); use=Pulse.Spec.GC.GraphBridge.fst(98,8-98,28)
                                                                                (=
                                                                                 (Pulse.Spec.GC.Object.wosize_of_object
                                                                                  (FStar.Seq.Properties.head
                                                                                   U_zero
                                                                                   Pulse.Spec.GC.Base.hp_addr
                                                                                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                  x_e246fc25c9201731c203dc9e18738560_0)
                                                                                 @x20))
                                                                               ;; def=Prims.fst(493,29-493,100); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                               (and
                                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                (or
                                                                                 label_13
                                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                 (Valid
                                                                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(32,14-32,38); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                  (Pulse.Spec.GC.Fields.well_formed_object
                                                                                   x_e246fc25c9201731c203dc9e18738560_0
                                                                                   (FStar.Seq.Properties.head
                                                                                    U_zero
                                                                                    Pulse.Spec.GC.Base.hp_addr
                                                                                    x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                (or
                                                                                 label_14
                                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(32,42-32,84); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                 (<=
                                                                                  (BoxInt_proj_0
                                                                                   (FStar.UInt64.v
                                                                                    (Pulse.Spec.GC.Object.wosize_of_object
                                                                                     (FStar.Seq.Properties.head
                                                                                      U_zero
                                                                                      Pulse.Spec.GC.Base.hp_addr
                                                                                      x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                     x_e246fc25c9201731c203dc9e18738560_0)))
                                                                                  (BoxInt_proj_0
                                                                                   (FStar.UInt64.v
                                                                                    (Pulse.Spec.GC.Object.wosize_of_object
                                                                                     (FStar.Seq.Properties.head
                                                                                      U_zero
                                                                                      Pulse.Spec.GC.Base.hp_addr
                                                                                      x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                     x_e246fc25c9201731c203dc9e18738560_0)))))
                                                                                ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(99,25-99,50)
                                                                                (forall
                                                                                  ((@x21 Term))
                                                                                 (! (implies
                                                                                   (and
                                                                                    (HasType
                                                                                     @x21
                                                                                     Pulse.Spec.GC.Graph.edge_list)
                                                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(99,8-99,63); use=Pulse.Spec.GC.GraphBridge.fst(99,8-99,63)
                                                                                    (=
                                                                                     (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                                                                                      x_e246fc25c9201731c203dc9e18738560_0
                                                                                      (FStar.Seq.Properties.head
                                                                                       U_zero
                                                                                       Pulse.Spec.GC.Base.hp_addr
                                                                                       x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                      (Pulse.Spec.GC.Object.wosize_of_object
                                                                                       (FStar.Seq.Properties.head
                                                                                        U_zero
                                                                                        Pulse.Spec.GC.Base.hp_addr
                                                                                        x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                       x_e246fc25c9201731c203dc9e18738560_0)
                                                                                      (FStar.UInt64.uint_to_t
                                                                                       (BoxInt 0)))
                                                                                     @x21))
                                                                                   ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                   (and
                                                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                    (forall
                                                                                      ((@x22 Term))
                                                                                     (! (implies
                                                                                       (HasType
                                                                                        @x22
                                                                                        Pulse.Spec.GC.Base.hp_addr)
                                                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(76,11-81,54); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                       (and
                                                                                        ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                        (or
                                                                                         label_15
                                                                                         ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                         (Valid
                                                                                          ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                          (Prims.hasEq
                                                                                           U_zero
                                                                                           Pulse.Spec.GC.Base.hp_addr)))
                                                                                        ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                        (forall
                                                                                          ((@x23
                                                                                            Term))
                                                                                         (! (implies
                                                                                           (and
                                                                                            (HasType
                                                                                             @x23
                                                                                             (Tm_type
                                                                                              U_zero))
                                                                                            ;; def=FStar.Seq.Properties.fsti(77,10-77,11); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                            (=
                                                                                             Pulse.Spec.GC.Base.hp_addr
                                                                                             @x23))
                                                                                           ;; def=FStar.Seq.Properties.fsti(42,28-42,40); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                           (or
                                                                                            label_16
                                                                                            ;; def=FStar.Seq.Properties.fsti(42,28-42,40); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                            (>
                                                                                             (BoxInt_proj_0
                                                                                              (FStar.Seq.Base.length
                                                                                               U_zero
                                                                                               Pulse.Spec.GC.Base.hp_addr
                                                                                               x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                             (BoxInt_proj_0
                                                                                              (BoxInt
                                                                                               0)))))
                                                                                          :qid
                                                                                           @query.27))
                                                                                        (implies
                                                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(76,11-76,33); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                         (BoxBool_proj_0
                                                                                          (FStar.Seq.Properties.mem
                                                                                           Pulse.Spec.GC.Base.hp_addr
                                                                                           @x22
                                                                                           (FStar.Seq.Properties.tail
                                                                                            U_zero
                                                                                            Pulse.Spec.GC.Base.hp_addr
                                                                                            x_a43c9a43db9e9f97f09b6905c39a534e_1)))
                                                                                         ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                         (or
                                                                                          label_17
                                                                                          ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                          (Valid
                                                                                           ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,28-101,39)
                                                                                           (Prims.hasEq
                                                                                            U_zero
                                                                                            Pulse.Spec.GC.Base.hp_addr))))))
                                                                                      :qid @query.26))
                                                                                    ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                    (forall
                                                                                      ((@x22 Term))
                                                                                     (! (implies
                                                                                       (and
                                                                                        (HasType
                                                                                         @x22
                                                                                         Tm_arrow_bbad94ce90b1b3329e5cd6b428840b8c)
                                                                                        ;; def=FStar.Classical.fsti(240,30-240,31); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                        (=
                                                                                         Tm_abs_73b9128286c767d273451036b15bab18
                                                                                         @x22))
                                                                                       ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                       (and
                                                                                        ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                        (or
                                                                                         label_18
                                                                                         ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                         (Valid
                                                                                          ;; def=Prims.fst(81,23-81,30); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                          (Prims.hasEq
                                                                                           U_zero
                                                                                           Pulse.Spec.GC.Base.hp_addr)))
                                                                                        ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                        (forall
                                                                                          ((@x23
                                                                                            Term))
                                                                                         (! (implies
                                                                                           (and
                                                                                            (HasType
                                                                                             @x23
                                                                                             (Tm_type
                                                                                              U_zero))
                                                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(75,18-81,54); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                            (=
                                                                                             Pulse.Spec.GC.Base.hp_addr
                                                                                             @x23))
                                                                                           ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                           (and
                                                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(75,39-75,55); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                            (or
                                                                                             label_19
                                                                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(75,39-75,55); use=Pulse.Spec.GC.GraphBridge.fst(101,40-101,44)
                                                                                             (>
                                                                                              (BoxInt_proj_0
                                                                                               (FStar.Seq.Base.length
                                                                                                U_zero
                                                                                                Pulse.Spec.GC.Base.hp_addr
                                                                                                x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                              (BoxInt_proj_0
                                                                                               (BoxInt
                                                                                                0))))
                                                                                            ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                            (forall
                                                                                              ((@x24
                                                                                                Term))
                                                                                             (! (implies
                                                                                               (and
                                                                                                (HasType
                                                                                                 @x24
                                                                                                 (FStar.Seq.Base.seq
                                                                                                  U_zero
                                                                                                  Pulse.Spec.GC.Base.hp_addr))
                                                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(75,30-81,41); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                (=
                                                                                                 x_a43c9a43db9e9f97f09b6905c39a534e_1
                                                                                                 @x24))
                                                                                               ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                               (forall
                                                                                                 ((@x25
                                                                                                   Term))
                                                                                                (! (implies
                                                                                                  (HasType
                                                                                                   @x25
                                                                                                   Tm_arrow_887539824376a20dbb4b47f159ed6152)
                                                                                                  ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(101,14-101,26)
                                                                                                  (forall
                                                                                                    ((@x26
                                                                                                      Term))
                                                                                                   (! (implies
                                                                                                     (and
                                                                                                      (HasType
                                                                                                       @x26
                                                                                                       Prims.unit)
                                                                                                      ;; def=FStar.Classical.fsti(241,12-241,32); use=Pulse.Spec.GC.GraphBridge.fst(101,14-101,26)
                                                                                                      (forall
                                                                                                        ((@x27
                                                                                                          Term))
                                                                                                       (! (implies
                                                                                                         (and
                                                                                                          (HasType
                                                                                                           @x27
                                                                                                           Pulse.Spec.GC.Base.hp_addr)
                                                                                                          ;; def=Pulse.Spec.GC.GraphBridge.fst(76,11-76,33); use=Pulse.Spec.GC.GraphBridge.fst(101,14-101,26)
                                                                                                          (BoxBool_proj_0
                                                                                                           (FStar.Seq.Properties.mem
                                                                                                            Pulse.Spec.GC.Base.hp_addr
                                                                                                            @x27
                                                                                                            (FStar.Seq.Properties.tail
                                                                                                             U_zero
                                                                                                             Pulse.Spec.GC.Base.hp_addr
                                                                                                             x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(76,38-76,49); use=Pulse.Spec.GC.GraphBridge.fst(101,14-101,26)
                                                                                                         (BoxBool_proj_0
                                                                                                          (FStar.Seq.Properties.mem
                                                                                                           Pulse.Spec.GC.Base.hp_addr
                                                                                                           @x27
                                                                                                           x_a43c9a43db9e9f97f09b6905c39a534e_1)))
                                                                                                        :qid
                                                                                                         @query.33)))
                                                                                                     ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                     (and
                                                                                                      ;; def=FStar.Seq.Properties.fsti(42,28-42,40); use=Pulse.Spec.GC.GraphBridge.fst(102,51-102,55)
                                                                                                      (or
                                                                                                       label_20
                                                                                                       ;; def=FStar.Seq.Properties.fsti(42,28-42,40); use=Pulse.Spec.GC.GraphBridge.fst(102,51-102,55)
                                                                                                       (>
                                                                                                        (BoxInt_proj_0
                                                                                                         (FStar.Seq.Base.length
                                                                                                          U_zero
                                                                                                          Pulse.Spec.GC.Base.hp_addr
                                                                                                          x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                                        (BoxInt_proj_0
                                                                                                         (BoxInt
                                                                                                          0))))
                                                                                                      ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                      (forall
                                                                                                        ((@x27
                                                                                                          Term))
                                                                                                       (! (implies
                                                                                                         (and
                                                                                                          (HasType
                                                                                                           @x27
                                                                                                           (FStar.Seq.Base.seq
                                                                                                            U_zero
                                                                                                            Pulse.Spec.GC.Base.hp_addr))
                                                                                                          ;; def=FStar.Seq.Properties.fsti(42,20-42,21); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                          (=
                                                                                                           x_a43c9a43db9e9f97f09b6905c39a534e_1
                                                                                                           @x27))
                                                                                                         ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                         (forall
                                                                                                           ((@x28
                                                                                                             Term))
                                                                                                          (! (implies
                                                                                                            (and
                                                                                                             (HasType
                                                                                                              @x28
                                                                                                              (FStar.Seq.Base.seq
                                                                                                               U_zero
                                                                                                               Pulse.Spec.GC.Base.hp_addr))
                                                                                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(81,37-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                             (=
                                                                                                              (FStar.Seq.Properties.tail
                                                                                                               U_zero
                                                                                                               Pulse.Spec.GC.Base.hp_addr
                                                                                                               x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                                              @x28))
                                                                                                            ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                            (and
                                                                                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(102,41-102,56)
                                                                                                             (or
                                                                                                              label_21
                                                                                                              ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(102,41-102,56)
                                                                                                              (Valid
                                                                                                               ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(102,41-102,56)
                                                                                                               (Prims.precedes
                                                                                                                U_zero
                                                                                                                U_zero
                                                                                                                Prims.nat
                                                                                                                Prims.nat
                                                                                                                (FStar.Seq.Base.length
                                                                                                                 U_zero
                                                                                                                 Pulse.Spec.GC.Base.hp_addr
                                                                                                                 (FStar.Seq.Properties.tail
                                                                                                                  U_zero
                                                                                                                  Pulse.Spec.GC.Base.hp_addr
                                                                                                                  x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                                                (FStar.Seq.Base.length
                                                                                                                 U_zero
                                                                                                                 Pulse.Spec.GC.Base.hp_addr
                                                                                                                 x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                                                             ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                             (forall
                                                                                                               ((@x29
                                                                                                                 Term))
                                                                                                              (! (implies
                                                                                                                (and
                                                                                                                 (HasType
                                                                                                                  @x29
                                                                                                                  Tm_refine_4a81764065a4360e3f4d7b2c4beaa311)
                                                                                                                 ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                                 (=
                                                                                                                  @x29
                                                                                                                  (FStar.Seq.Properties.tail
                                                                                                                   U_zero
                                                                                                                   Pulse.Spec.GC.Base.hp_addr
                                                                                                                   x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(81,37-102,56); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                                 (=
                                                                                                                  (FStar.Seq.Properties.tail
                                                                                                                   U_zero
                                                                                                                   Pulse.Spec.GC.Base.hp_addr
                                                                                                                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                                                                                                                  @x29))
                                                                                                                ;; def=Prims.fst(493,29-493,100); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                (and
                                                                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                 (or
                                                                                                                  label_22
                                                                                                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                  (Valid
                                                                                                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                   (Pulse.Spec.GC.GraphBridge.all_objects_well_formed
                                                                                                                    x_e246fc25c9201731c203dc9e18738560_0)))
                                                                                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                 (or
                                                                                                                  label_23
                                                                                                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                  (Valid
                                                                                                                   ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                   (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
                                                                                                                    x_e246fc25c9201731c203dc9e18738560_0
                                                                                                                    (FStar.Seq.Properties.tail
                                                                                                                     U_zero
                                                                                                                     Pulse.Spec.GC.Base.hp_addr
                                                                                                                     x_a43c9a43db9e9f97f09b6905c39a534e_1))))
                                                                                                                 ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(102,21-102,38)
                                                                                                                 (forall
                                                                                                                   ((@x30
                                                                                                                     Term))
                                                                                                                  (! (implies
                                                                                                                    (and
                                                                                                                     (HasType
                                                                                                                      @x30
                                                                                                                      Pulse.Spec.GC.Graph.edge_list)
                                                                                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(102,8-102,56); use=Pulse.Spec.GC.GraphBridge.fst(102,8-102,56)
                                                                                                                     (=
                                                                                                                      (Pulse.Spec.GC.GraphBridge.collect_all_edges
                                                                                                                       x_e246fc25c9201731c203dc9e18738560_0
                                                                                                                       (FStar.Seq.Properties.tail
                                                                                                                        U_zero
                                                                                                                        Pulse.Spec.GC.Base.hp_addr
                                                                                                                        x_a43c9a43db9e9f97f09b6905c39a534e_1))
                                                                                                                      @x30))
                                                                                                                    ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                                    (forall
                                                                                                                      ((@x31
                                                                                                                        Term))
                                                                                                                     (! (implies
                                                                                                                       (HasType
                                                                                                                        @x31
                                                                                                                        Pulse.Spec.GC.Graph.edge_list)
                                                                                                                       ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                                       (Valid
                                                                                                                        ;; def=Prims.fst(459,90-459,102); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
                                                                                                                        (ApplyTT
                                                                                                                         @x1
                                                                                                                         @x31)))
                                                                                                                      :qid
                                                                                                                       @query.38)))
                                                                                                                   :qid
                                                                                                                    @query.37))))
                                                                                                               :qid
                                                                                                                @query.36))))
                                                                                                           :qid
                                                                                                            @query.35)))
                                                                                                        :qid
                                                                                                         @query.34))))
                                                                                                    :qid
                                                                                                     @query.32)))
                                                                                                 :qid
                                                                                                  @query.31)))
                                                                                              :qid
                                                                                               @query.30))))
                                                                                          :qid
                                                                                           @query.29))))
                                                                                      :qid @query.28))))
                                                                                  :qid @query.25))))
                                                                              :qid @query.24))))
                                                                          :qid @query.23)))
                                                                       :qid @query.22))))
                                                                   :qid @query.21))))
                                                               :qid @query.20)))
                                                            :qid @query.19)))
                                                         :qid @query.18)))
                                                      :qid @query.17))))
                                                  :qid @query.16))))
                                              :qid @query.15))))
                                          :qid @query.14)))
                                       :qid @query.13)))
                                    :qid @query.12))))
                                :qid @query.11)))
                             :qid @query.10))))
                         :qid @query.9))))
                     :qid @query.8)))
                  :qid @query.7))))
              :qid @query.6)))))
         :qid @query.2)))
      :qid @query))
    ;; def=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
    (forall ((@x0 Term))
     (! (implies
       (and
        (HasType @x0 (Prims.pure_post U_zero Pulse.Spec.GC.Graph.edge_list))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Pulse.Spec.GC.GraphBridge.all_objects_well_formed x_e246fc25c9201731c203dc9e18738560_0))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (Valid
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
          x_e246fc25c9201731c203dc9e18738560_0
          x_a43c9a43db9e9f97f09b6905c39a534e_1))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (forall ((@x1 Term))
         (! (implies
           (or label_24 (HasType @x1 Pulse.Spec.GC.Graph.edge_list))
           ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
           (Valid
            ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (ApplyTT @x0 @x1)))
          :pattern
           (;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (Valid
             ;; def=Prims.fst(493,85-493,99); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
             (ApplyTT @x0 @x1)))
          :qid @query.40)))
       ;; def=Prims.fst(493,29-493,100); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
       (and
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (or
         label_25
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Valid
          ;; def=Pulse.Spec.GC.GraphBridge.fst(83,14-83,39); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
          (Pulse.Spec.GC.GraphBridge.all_objects_well_formed x_e246fc25c9201731c203dc9e18738560_0)))
        ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (or
         label_26
         ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
         (Valid
          ;; def=Pulse.Spec.GC.GraphBridge.fst(83,43-83,72); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
          (Pulse.Spec.GC.GraphBridge.objs_subset_of_objects
           x_e246fc25c9201731c203dc9e18738560_0
           x_a43c9a43db9e9f97f09b6905c39a534e_1)))
        ;; def=Prims.fst(493,36-493,100); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
        (forall ((@x1 Term))
         (! (implies
           (and
            (HasType @x1 Pulse.Spec.GC.Graph.edge_list)
            ;; def=Pulse.Spec.GC.GraphBridge.fst(82,10-103,40); use=Pulse.Spec.GC.GraphBridge.fst(87,2-103,40)
            (=
             @x1
             (let
               ((@lb2
                 (Prims.op_Equality
                  Prims.int
                  (FStar.Seq.Base.length
                   U_zero
                   Pulse.Spec.GC.Base.hp_addr
                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                  (BoxInt 0))))
              (ite
               (= @lb2 (BoxBool true))
               (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.edge)
               (FStar.Seq.Base.append
                U_zero
                Pulse.Spec.GC.Graph.edge
                (Pulse.Spec.GC.GraphBridge.collect_edges_from_object
                 x_e246fc25c9201731c203dc9e18738560_0
                 (FStar.Seq.Properties.head
                  U_zero
                  Pulse.Spec.GC.Base.hp_addr
                  x_a43c9a43db9e9f97f09b6905c39a534e_1)
                 (Pulse.Spec.GC.Object.wosize_of_object
                  (FStar.Seq.Properties.head
                   U_zero
                   Pulse.Spec.GC.Base.hp_addr
                   x_a43c9a43db9e9f97f09b6905c39a534e_1)
                  x_e246fc25c9201731c203dc9e18738560_0)
                 (FStar.UInt64.uint_to_t (BoxInt 0)))
                (Pulse.Spec.GC.GraphBridge.collect_all_edges
                 x_e246fc25c9201731c203dc9e18738560_0
                 (FStar.Seq.Properties.tail
                  U_zero
                  Pulse.Spec.GC.Base.hp_addr
                  x_a43c9a43db9e9f97f09b6905c39a534e_1)))))))
           ;; def=Prims.fst(364,2-364,58); use=Prims.fst(434,19-434,31)
           (forall ((@x2 Term))
            (! (implies
              (and
               (HasType @x2 Pulse.Spec.GC.Graph.edge_list)
               ;; def=Prims.fst(364,26-364,41); use=Prims.fst(434,19-434,31)
               (= @x2 @x1))
              ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
              (Valid
               ;; def=Prims.fst(364,46-364,58); use=Prims.fst(434,19-434,31)
               (ApplyTT @x0 @x2)))
             :qid @query.42)))
          :qid @query.41))))
      :qid @query.39))))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_26")
(eval label_26)
(echo "label_25")
(eval label_25)
(echo "label_24")
(eval label_24)
(echo "label_23")
(eval label_23)
(echo "label_22")
(eval label_22)
(echo "label_21")
(eval label_21)
(echo "label_20")
(eval label_20)
(echo "label_19")
(eval label_19)
(echo "label_18")
(eval label_18)
(echo "label_17")
(eval label_17)
(echo "label_16")
(eval label_16)
(echo "label_15")
(eval label_15)
(echo "label_14")
(eval label_14)
(echo "label_13")
(eval label_13)
(echo "label_12")
(eval label_12)
(echo "label_11")
(eval label_11)
(echo "label_10")
(eval label_10)
(echo "label_9")
(eval label_9)
(echo "label_8")
(eval label_8)
(echo "label_7")
(eval label_7)
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.collect_all_edges, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.12.15~dev -- commit hash: be8b3217ae8f82b3450f1538c64f7685bd586619
; Z3 version (according to F*): 4.13.3

(pop) ;; 2}pop
(declare-fun Prims.nonzero () Term)
(declare-fun Prims.op_Negation (Term) Term)
(declare-fun Pulse.Spec.GC.Graph.is_vertex_set (Term) Term)
; Fuel-instrumented function name
(declare-fun Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented (Fuel Term) Term)
(declare-fun Pulse.Spec.GC.Graph.vertex_list () Term)
(declare-fun Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f () Term)
; Correspondence of recursive function to instrumented version
;;; Fact-ids: Name Pulse.Spec.GC.Graph.is_vertex_set; Namespace Pulse.Spec.GC.Graph
(assert
 (! ;; def=Pulse.Spec.GC.Graph.fst(59,8-59,21); use=Pulse.Spec.GC.Graph.fst(59,8-59,21)
  (forall ((@x0 Term))
   (! (=
     (Pulse.Spec.GC.Graph.is_vertex_set @x0)
     (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented MaxFuel @x0))
    :pattern ((Pulse.Spec.GC.Graph.is_vertex_set @x0))
    :qid @fuel_correspondence_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
  :named @fuel_correspondence_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
; Fuel irrelevance
;;; Fact-ids: Name Pulse.Spec.GC.Graph.is_vertex_set; Namespace Pulse.Spec.GC.Graph
(assert
 (! ;; def=Pulse.Spec.GC.Graph.fst(59,8-59,21); use=Pulse.Spec.GC.Graph.fst(59,8-59,21)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (=
     (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented (SFuel @u0) @x1)
     (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented ZFuel @x1))
    :pattern ((Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented (SFuel @u0) @x1))
    :qid @fuel_irrelevance_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
  :named @fuel_irrelevance_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
; Equation for Prims.nonzero
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (= Prims.nonzero Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f) :named equation_Prims.nonzero))
; Equation for Pulse.Spec.GC.Graph.vertex_list
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (= Pulse.Spec.GC.Graph.vertex_list (FStar.Seq.Base.seq U_zero Pulse.Spec.GC.Graph.vertex_id))
  :named equation_Pulse.Spec.GC.Graph.vertex_list))
; Equation for fuel-instrumented recursive function: Pulse.Spec.GC.Graph.is_vertex_set
;;; Fact-ids: Name Pulse.Spec.GC.Graph.is_vertex_set; Namespace Pulse.Spec.GC.Graph
(assert
 (! ;; def=Pulse.Spec.GC.Graph.fst(59,8-59,21); use=Pulse.Spec.GC.Graph.fst(59,8-59,21)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasType @x1 Pulse.Spec.GC.Graph.vertex_list)
     (=
      (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented (SFuel @u0) @x1)
      (let
        ((@lb2
          (Prims.op_Equality
           Prims.int
           (FStar.Seq.Base.length U_zero Pulse.Spec.GC.Graph.vertex_id @x1)
           (BoxInt 0))))
       (ite
        (= @lb2 (BoxBool true))
        (BoxBool true)
        (Prims.op_AmpAmp
         (Prims.op_Negation
          (FStar.Seq.Properties.mem
           Pulse.Spec.GC.Graph.vertex_id
           (FStar.Seq.Properties.head U_zero Pulse.Spec.GC.Graph.vertex_id @x1)
           (FStar.Seq.Properties.tail U_zero Pulse.Spec.GC.Graph.vertex_id @x1)))
         (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented
          @u0
          (FStar.Seq.Properties.tail U_zero Pulse.Spec.GC.Graph.vertex_id @x1)))))))
    :weight 0
    :pattern ((Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented (SFuel @u0) @x1))
    :qid equation_with_fuel_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
  :named equation_with_fuel_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
; function token typing
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (HasType Prims.nonzero (Tm_type U_zero)) :named function_token_typing_Prims.nonzero))
; function token typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.vertex_list (Tm_type U_zero))
  :named function_token_typing_Pulse.Spec.GC.Graph.vertex_list))
; haseq for Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq U_zero Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
   (Valid (Prims.hasEq U_zero Prims.int)))
  :named haseqTm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
;;; Fact-ids: Name Prims.op_Negation; Namespace Prims
(assert
 (! ;; def=Prims.fst(542,4-542,15); use=Prims.fst(542,4-542,15)
  (forall ((@x0 Term))
   (! (= (Prims.op_Negation @x0) (BoxBool (not (BoxBool_proj_0 @x0))))
    :pattern ((Prims.op_Negation @x0))
    :qid primitive_Prims.op_Negation))
  :named primitive_Prims.op_Negation))
; refinement_interpretation
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! ;; def=Prims.fst(688,15-688,29); use=Prims.fst(688,15-688,29)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(688,22-688,28); use=Prims.fst(688,22-688,28)
      (not (= @x1 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
    :qid refinement_interpretation_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
  :named refinement_interpretation_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
; refinement kinding
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (HasType Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f (Tm_type U_zero))
  :named refinement_kinding_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
; Typing correspondence of token to term
;;; Fact-ids: Name Pulse.Spec.GC.Graph.is_vertex_set; Namespace Pulse.Spec.GC.Graph
(assert
 (! ;; def=Pulse.Spec.GC.Graph.fst(59,8-59,21); use=Pulse.Spec.GC.Graph.fst(59,8-59,21)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasType @x1 Pulse.Spec.GC.Graph.vertex_list)
     (HasType (Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented @u0 @x1) Prims.bool))
    :pattern ((Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented @u0 @x1))
    :qid token_correspondence_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
  :named token_correspondence_Pulse.Spec.GC.Graph.is_vertex_set.fuel_instrumented))
; free var typing
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (HasType Prims.nonzero (Tm_type U_zero)) :named typing_Prims.nonzero))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.is_vertex_set; Namespace Pulse.Spec.GC.Graph
(assert
 (! ;; def=Pulse.Spec.GC.Graph.fst(59,8-59,21); use=Pulse.Spec.GC.Graph.fst(59,8-59,21)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Pulse.Spec.GC.Graph.vertex_list)
     (HasType (Pulse.Spec.GC.Graph.is_vertex_set @x0) Prims.bool))
    :pattern ((Pulse.Spec.GC.Graph.is_vertex_set @x0))
    :qid typing_Pulse.Spec.GC.Graph.is_vertex_set))
  :named typing_Pulse.Spec.GC.Graph.is_vertex_set))
; free var typing
;;; Fact-ids: Name Pulse.Spec.GC.Graph.vertex_list; Namespace Pulse.Spec.GC.Graph
(assert
 (! (HasType Pulse.Spec.GC.Graph.vertex_list (Tm_type U_zero))
  :named typing_Pulse.Spec.GC.Graph.vertex_list))
(push) ;; push{2
; start : Pulse.Spec.GC.Base.hp_addr (Pulse.Spec.GC.Base.hp_addr)
(declare-fun x_c39bed69b0e6a97dd42e9a16413dbcb1_0 () Term)
; binder_x_c39bed69b0e6a97dd42e9a16413dbcb1_0
;;; Fact-ids: 
(assert
 (! (HasType x_c39bed69b0e6a97dd42e9a16413dbcb1_0 Pulse.Spec.GC.Base.hp_addr)
  :named binder_x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
; g : Pulse.Spec.GC.Base.heap (Pulse.Spec.GC.Base.heap)
(declare-fun x_e246fc25c9201731c203dc9e18738560_1 () Term)
; binder_x_e246fc25c9201731c203dc9e18738560_1
;;; Fact-ids: 
(assert
 (! (HasType x_e246fc25c9201731c203dc9e18738560_1 Pulse.Spec.GC.Base.heap)
  :named binder_x_e246fc25c9201731c203dc9e18738560_1))
; Uninterpreted function symbol for impure function
(declare-fun Pulse.Spec.GC.GraphBridge.objects_no_duplicates (Term Term) Term)
; Uninterpreted name for impure function
(declare-fun Pulse.Spec.GC.GraphBridge.objects_no_duplicates@tok () Term)
(declare-fun label_22 () Bool)
(declare-fun label_21 () Bool)
(declare-fun label_20 () Bool)
(declare-fun label_19 () Bool)
(declare-fun label_18 () Bool)
(declare-fun label_17 () Bool)
(declare-fun label_16 () Bool)
(declare-fun label_15 () Bool)
(declare-fun label_14 () Bool)
(declare-fun label_13 () Bool)
(declare-fun label_12 () Bool)
(declare-fun label_11 () Bool)
(declare-fun label_10 () Bool)
(declare-fun label_9 () Bool)
(declare-fun label_8 () Bool)
(declare-fun label_7 () Bool)
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit).
;       Pulse.Spec.GC.Graph.is_vertex_set (Pulse.Spec.GC.Fields.objects start g) ==> p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (FStar.UInt64.v start + 8 >= FStar.Seq.Base.length g == true ==>
;         (forall (pure_result: Prims.unit).
;             Pulse.Spec.GC.Graph.is_vertex_set seq![] ==> k pure_result)) /\
;       (~(FStar.UInt64.v start + 8 >= FStar.Seq.Base.length g = true) ==>
;         (forall (b: Prims.bool).
;             FStar.UInt64.v start + 8 >= FStar.Seq.Base.length g == b ==>
;             (forall (k: Prims.pure_post Prims.unit).
;                 (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} k x ==> k x) ==>
;                 ((FStar.UInt64.v start +
;                   (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                               start)) +
;                     1) *
;                   8 >
;                   FStar.Seq.Base.length g ||
;                   FStar.UInt64.v start +
;                   (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                               start)) +
;                     1) *
;                   8 >=
;                   Prims.pow2 64) ==
;                   true ==>
;                   (forall (pure_result: Prims.unit).
;                       Pulse.Spec.GC.Graph.is_vertex_set seq![] ==> k pure_result)) /\
;                 (~((FStar.UInt64.v start +
;                     (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                                 start)) +
;                       1) *
;                     8 >
;                     FStar.Seq.Base.length g ||
;                     FStar.UInt64.v start +
;                     (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                                 start)) +
;                       1) *
;                     8 >=
;                     Prims.pow2 64) =
;                     true) ==>
;                   (forall (b: Prims.bool).
;                       (FStar.UInt64.v start +
;                       (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                                   start)) +
;                         1) *
;                       8 >
;                       FStar.Seq.Base.length g ||
;                       FStar.UInt64.v start +
;                       (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize (Pulse.Spec.GC.Heap.read_word g
;                                   start)) +
;                         1) *
;                       8 >=
;                       Prims.pow2 64) ==
;                       b ==>
;                       (Prims.pow2 64 > 0 ==> Prims.pow2 64 <> 0) /\
;                       (forall (return_val: Prims.nonzero).
;                           return_val == Prims.pow2 64 ==>
;                           (forall (any_result: Prims.int).
;                               (FStar.UInt64.v start + 8) % Prims.pow2 64 == any_result ==>
;                               (forall (any_result: Prims.bool).
;                                   FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address start) =
;                                   (FStar.UInt64.v start + 8) % Prims.pow2 64 ==
;                                   any_result ==>
;                                   (forall (any_result: Prims.logical).
;                                       FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address start) =
;                                       (FStar.UInt64.v start + 8) % Prims.pow2 64 ==
;                                       any_result ==>
;                                       FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address start) =
;                                       (FStar.UInt64.v start + 8) % Prims.pow2 64 /\
;                                       (forall (pure_result: Prims.unit).
;                                           FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address start) =
;                                           (FStar.UInt64.v start + 8) % Prims.pow2 64 ==>
;                                           FStar.UInt64.v start + 8 < Pulse.Spec.GC.Base.heap_size /\
;                                           (forall (pure_result: Prims.unit).
;                                               FStar.UInt64.v start + 8 <
;                                               Pulse.Spec.GC.Base.heap_size ==>
;                                               FStar.UInt64.v start + 8 < Prims.pow2 64 /\
;                                               (forall (pure_result: Prims.unit).
;                                                   FStar.UInt64.v start + 8 < Prims.pow2 64 ==>
;                                                   FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address start
;                                                       ) =
;                                                   FStar.UInt64.v start + 8 /\
;                                                   (forall (pure_result: Prims.unit).
;                                                       FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                             start) =
;                                                       FStar.UInt64.v start + 8 ==>
;                                                       FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                             start) <
;                                                       Pulse.Spec.GC.Base.heap_size /\
;                                                       (forall (pure_result: Prims.unit).
;                                                           FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                 start) <
;                                                           Pulse.Spec.GC.Base.heap_size ==>
;                                                           FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                 start) %
;                                                           8 =
;                                                           0 /\
;                                                           (forall (pure_result: Prims.unit).
;                                                               FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                     start) %
;                                                               8 =
;                                                               0 ==>
;                                                               FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                     start) >=
;                                                               0 /\
;                                                               FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                     start) <
;                                                               Pulse.Spec.GC.Base.heap_size /\
;                                                               FStar.UInt64.v (Pulse.Spec.GC.Fields.obj_address
;                                                                     start) %
;                                                               FStar.UInt64.v Pulse.Spec.GC.Base.mword
;                                                                ==
;                                                               0 /\
;                                                               (forall (any_result: FStar.UInt64.t).
;                                                                   Pulse.Spec.GC.Fields.obj_address start
;                                                                    ==
;                                                                   any_result ==>
;                                                                   (forall (k:
;                                                                       Prims.pure_post Prims.unit).
;                                                                       (forall (x: Prims.unit).
;                                                                           {:pattern
;                                                                           Prims.guard_free (k x)}
;                                                                           k x ==> k x) ==>
;                                                                       (FStar.UInt64.v start +
;                                                                         (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                 (Pulse.Spec.GC.Heap.read_word
;                                                                                     g
;                                                                                     start)) +
;                                                                           1) *
;                                                                         8 >=
;                                                                         Pulse.Spec.GC.Base.heap_size ==
;                                                                         true ==>
;                                                                         (forall (pure_result:
;                                                                             Prims.unit).
;                                                                             Pulse.Spec.GC.Graph.is_vertex_set
;                                                                               (FStar.Seq.Base.create
;                                                                                   1
;                                                                                   (Pulse.Spec.GC.Fields.obj_address
;                                                                                       start)) ==>
;                                                                             k pure_result)) /\
;                                                                       (~(FStar.UInt64.v start +
;                                                                           (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                   (Pulse.Spec.GC.Heap.read_word
;                                                                                       g
;                                                                                       start)) +
;                                                                             1) *
;                                                                           8 >=
;                                                                           Pulse.Spec.GC.Base.heap_size =
;                                                                           true) ==>
;                                                                         (forall (b: Prims.bool).
;                                                                             FStar.UInt64.v start +
;                                                                             (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                     (Pulse.Spec.GC.Heap.read_word
;                                                                                         g
;                                                                                         start)) +
;                                                                               1) *
;                                                                             8 >=
;                                                                             Pulse.Spec.GC.Base.heap_size ==
;                                                                             b ==>
;                                                                             FStar.UInt64.v start +
;                                                                             (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                     (Pulse.Spec.GC.Heap.read_word
;                                                                                         g
;                                                                                         start)) +
;                                                                               1) *
;                                                                             8 <
;                                                                             Pulse.Spec.GC.Base.heap_size /\
;                                                                             (forall (pure_result:
;                                                                                 Prims.unit).
;                                                                                 FStar.UInt64.v start +
;                                                                                 (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                         (Pulse.Spec.GC.Heap.read_word
;                                                                                             g
;                                                                                             start)) +
;                                                                                   1) *
;                                                                                 8 <
;                                                                                 Pulse.Spec.GC.Base.heap_size ==>
;                                                                                 (FStar.UInt64.v start
;                                                                                    +
;                                                                                   (FStar.UInt64.v (Pulse.Spec.GC.Object.getWosize
;                                                                                           (Pulse.Spec.GC.Heap.read_word
;                                                                                               g
;                                                                                               start)
;                                                                                       ) +
;                                                                                     1) *
;                                                                                   8) %
;                                                                                 8 =
;                                                                                 0 /\
;                                                                                 (forall (pure_result:
;                                                                                     Prims.unit).
;                                                                                     (FStar.UInt64.v start
;                                                                                        +
;                                                                                       (FStar.UInt64.v
;                                                                                           (Pulse.Spec.GC.Object.getWosize
;                                                                                               (Pulse.Spec.GC.Heap.read_word
;                                                                                                   g
;                                                                                                   start
;                                                                                                 )) +
;                                                                                         1) *
;                                                                                       8) %
;                                                                                     8 =
;                                                                                     0 ==>
;                                                                                     Prims.auto_squash
;                                                                                       (FStar.UInt.size
;                                                                                           (FStar.UInt64.v
;                                                                                               start +
;                                                                                             (FStar.UInt64.v
;                                                                                                 (Pulse.Spec.GC.Object.getWosize
;                                                                                                     (
;                                                                                                       Pulse.Spec.GC.Heap.read_word
;                                                                                                         g
;                                                                                                         start
; 
;                                                                                                     )
;                                                                                                   ) +
;                                                                                               1) *
;                                                                                             8)
;                                                                                           64) /\
;                                                                                     (forall (any_result:
;                                                                                         Prims.int).
;                                                                                         FStar.UInt64.v
;                                                                                           start +
;                                                                                         (FStar.UInt64.v
;                                                                                             (Pulse.Spec.GC.Object.getWosize
;                                                                                                 (Pulse.Spec.GC.Heap.read_word
;                                                                                                     g
;                                                                                                     start
;                                                                                                   )) +
;                                                                                           1) *
;                                                                                         8 ==
;                                                                                         any_result ==>
;                                                                                         (forall (pure_result:
;                                                                                             FStar.UInt64.t)
;                                                                                           .
;                                                                                             FStar.UInt64.v
;                                                                                               pure_result
;                                                                                              =
;                                                                                             FStar.UInt64.v
;                                                                                               start +
;                                                                                             (FStar.UInt64.v
;                                                                                                 (Pulse.Spec.GC.Object.getWosize
;                                                                                                     (
;                                                                                                       Pulse.Spec.GC.Heap.read_word
;                                                                                                         g
;                                                                                                         start
; 
;                                                                                                     )
;                                                                                                   ) +
;                                                                                               1) *
;                                                                                             8 ==>
;                                                                                             FStar.UInt64.uint_to_t
;                                                                                               (FStar.UInt64.v
;                                                                                                   start
;                                                                                                  +
;                                                                                                 (FStar.UInt64.v
;                                                                                                     (
;                                                                                                       Pulse.Spec.GC.Object.getWosize
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Heap.read_word
;                                                                                                             g
;                                                                                                             start
; 
;                                                                                                         )
; 
;                                                                                                     )
;                                                                                                    +
;                                                                                                   1) *
;                                                                                                 8) ==
;                                                                                             pure_result ==>
;                                                                                             FStar.UInt64.v
;                                                                                               (FStar.UInt64.uint_to_t
;                                                                                                   (FStar.UInt64.v
;                                                                                                       start
;                                                                                                      +
;                                                                                                     (
;                                                                                                       FStar.UInt64.v
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                 g
;                                                                                                                 start
; 
;                                                                                                             )
; 
;                                                                                                         )
;                                                                                                        +
;                                                                                                       1
;                                                                                                     ) *
;                                                                                                     8
;                                                                                                   )) >=
;                                                                                             0 /\
;                                                                                             FStar.UInt64.v
;                                                                                               (FStar.UInt64.uint_to_t
;                                                                                                   (FStar.UInt64.v
;                                                                                                       start
;                                                                                                      +
;                                                                                                     (
;                                                                                                       FStar.UInt64.v
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                 g
;                                                                                                                 start
; 
;                                                                                                             )
; 
;                                                                                                         )
;                                                                                                        +
;                                                                                                       1
;                                                                                                     ) *
;                                                                                                     8
;                                                                                                   )) <
;                                                                                             Pulse.Spec.GC.Base.heap_size /\
;                                                                                             FStar.UInt64.v
;                                                                                               (FStar.UInt64.uint_to_t
;                                                                                                   (FStar.UInt64.v
;                                                                                                       start
;                                                                                                      +
;                                                                                                     (
;                                                                                                       FStar.UInt64.v
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                 g
;                                                                                                                 start
; 
;                                                                                                             )
; 
;                                                                                                         )
;                                                                                                        +
;                                                                                                       1
;                                                                                                     ) *
;                                                                                                     8
;                                                                                                   )) %
;                                                                                             FStar.UInt64.v
;                                                                                               Pulse.Spec.GC.Base.mword
;                                                                                              ==
;                                                                                             0 /\
;                                                                                             (forall (return_val:
;                                                                                                 Pulse.Spec.GC.Base.hp_addr)
;                                                                                               .
;                                                                                                 return_val ==
;                                                                                                 FStar.UInt64.uint_to_t
;                                                                                                   (FStar.UInt64.v
;                                                                                                       start
;                                                                                                      +
;                                                                                                     (
;                                                                                                       FStar.UInt64.v
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                 g
;                                                                                                                 start
; 
;                                                                                                             )
; 
;                                                                                                         )
;                                                                                                        +
;                                                                                                       1
;                                                                                                     ) *
;                                                                                                     8
;                                                                                                   ) ==>
;                                                                                                 FStar.UInt64.uint_to_t
;                                                                                                   (FStar.UInt64.v
;                                                                                                       start
;                                                                                                      +
;                                                                                                     (
;                                                                                                       FStar.UInt64.v
;                                                                                                         (
;                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                 g
;                                                                                                                 start
; 
;                                                                                                             )
; 
;                                                                                                         )
;                                                                                                        +
;                                                                                                       1
;                                                                                                     ) *
;                                                                                                     8
;                                                                                                   ) ==
;                                                                                                 return_val ==>
;                                                                                                 FStar.Seq.Base.length
;                                                                                                   g -
;                                                                                                 FStar.UInt64.v
;                                                                                                   (FStar.UInt64.uint_to_t
;                                                                                                       (
;                                                                                                         FStar.UInt64.v
;                                                                                                           start
;                                                                                                          +
;                                                                                                         (
;                                                                                                           FStar.UInt64.v
;                                                                                                             (
;                                                                                                               Pulse.Spec.GC.Object.getWosize
;                                                                                                                 (
;                                                                                                                   Pulse.Spec.GC.Heap.read_word
;                                                                                                                     g
;                                                                                                                     start
; 
;                                                                                                                 )
; 
;                                                                                                             )
;                                                                                                            +
;                                                                                                           1
;                                                                                                         ) *
;                                                                                                         8
;                                                                                                       )
; 
;                                                                                                   ) <<
;                                                                                                 FStar.Seq.Base.length
;                                                                                                   g -
;                                                                                                 FStar.UInt64.v
;                                                                                                   start
;                                                                                                  /\
;                                                                                                 (forall
;                                                                                                     (any_result:
;                                                                                                     Pulse.Spec.GC.Base.heap)
;                                                                                                   .
;                                                                                                     g ==
;                                                                                                     any_result ==>
;                                                                                                     (
;                                                                                                       forall
;                                                                                                         (pure_result:
;                                                                                                         Prims.unit)
;                                                                                                       .
;                                                                                                         Pulse.Spec.GC.Graph.is_vertex_set
;                                                                                                           (
;                                                                                                             Pulse.Spec.GC.Fields.objects
;                                                                                                               (
;                                                                                                                 FStar.UInt64.uint_to_t
;                                                                                                                   (
;                                                                                                                     FStar.UInt64.v
;                                                                                                                       start
;                                                                                                                      +
;                                                                                                                     (
;                                                                                                                       FStar.UInt64.v
;                                                                                                                         (
;                                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                                             (
;                                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                                 g
;                                                                                                                                 start
; 
;                                                                                                                             )
; 
;                                                                                                                         )
;                                                                                                                        +
;                                                                                                                       1
;                                                                                                                     ) *
;                                                                                                                     8
;                                                                                                                   )
; 
;                                                                                                               )
;                                                                                                               g
; 
;                                                                                                           )
;                                                                                                          ==>
;                                                                                                         (
;                                                                                                           forall
;                                                                                                             (any_result:
;                                                                                                             FStar.Seq.Base.seq
;                                                                                                               Pulse.Spec.GC.Base.hp_addr
;                                                                                                             )
;                                                                                                           .
;                                                                                                             Pulse.Spec.GC.Fields.objects
;                                                                                                               (
;                                                                                                                 FStar.UInt64.uint_to_t
;                                                                                                                   (
;                                                                                                                     FStar.UInt64.v
;                                                                                                                       start
;                                                                                                                      +
;                                                                                                                     (
;                                                                                                                       FStar.UInt64.v
;                                                                                                                         (
;                                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                                             (
;                                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                                 g
;                                                                                                                                 start
; 
;                                                                                                                             )
; 
;                                                                                                                         )
;                                                                                                                        +
;                                                                                                                       1
;                                                                                                                     ) *
;                                                                                                                     8
;                                                                                                                   )
; 
;                                                                                                               )
;                                                                                                               g
;                                                                                                              ==
;                                                                                                             any_result ==>
;                                                                                                             FStar.UInt64.v
;                                                                                                               start
;                                                                                                              +
;                                                                                                             8 <=
;                                                                                                             FStar.Seq.Base.length
;                                                                                                               g
;                                                                                                              /\
;                                                                                                             (
;                                                                                                               forall
;                                                                                                                 (pure_result:
;                                                                                                                 Prims.unit)
;                                                                                                               .
;                                                                                                                 Pulse.Spec.GC.Graph.is_vertex_set
;                                                                                                                   (
;                                                                                                                     Pulse.Spec.GC.Fields.objects
;                                                                                                                       (
;                                                                                                                         FStar.UInt64.uint_to_t
;                                                                                                                           (
;                                                                                                                             FStar.UInt64.v
;                                                                                                                               start
;                                                                                                                              +
;                                                                                                                             (
;                                                                                                                               FStar.UInt64.v
;                                                                                                                                 (
;                                                                                                                                   Pulse.Spec.GC.Object.getWosize
;                                                                                                                                     (
;                                                                                                                                       Pulse.Spec.GC.Heap.read_word
;                                                                                                                                         g
;                                                                                                                                         start
; 
;                                                                                                                                     )
; 
;                                                                                                                                 )
;                                                                                                                                +
;                                                                                                                               1
;                                                                                                                             ) *
;                                                                                                                             8
;                                                                                                                           )
; 
;                                                                                                                       )
;                                                                                                                       g
; 
;                                                                                                                   )
;                                                                                                                  /\
;                                                                                                                 (
;                                                                                                                   forall
;                                                                                                                     (any_result:
;                                                                                                                     FStar.Seq.Base.seq
;                                                                                                                       Pulse.Spec.GC.Base.hp_addr
;                                                                                                                     )
;                                                                                                                   .
;                                                                                                                     Pulse.Spec.GC.Fields.objects
;                                                                                                                       (
;                                                                                                                         FStar.UInt64.uint_to_t
;                                                                                                                           (
;                                                                                                                             FStar.UInt64.v
;                                                                                                                               start
;                                                                                                                              +
;                                                                                                                             (
;                                                                                                                               FStar.UInt64.v
;                                                                                                                                 (
;                                                                                                                                   Pulse.Spec.GC.Object.getWosize
;                                                                                                                                     (
;                                                                                                                                       Pulse.Spec.GC.Heap.read_word
;                                                                                                                                         g
;                                                                                                                                         start
; 
;                                                                                                                                     )
; 
;                                                                                                                                 )
;                                                                                                                                +
;                                                                                                                               1
;                                                                                                                             ) *
;                                                                                                                             8
;                                                                                                                           )
; 
;                                                                                                                       )
;                                                                                                                       g
;                                                                                                                      ==
;                                                                                                                     any_result ==>
;                                                                                                                     Prims.op_Negation
;                                                                                                                       (
;                                                                                                                         FStar.Seq.Properties.mem
;                                                                                                                           (
;                                                                                                                             Pulse.Spec.GC.Fields.obj_address
;                                                                                                                               start
; 
;                                                                                                                           )
;                                                                                                                           (
;                                                                                                                             Pulse.Spec.GC.Fields.objects
;                                                                                                                               (
;                                                                                                                                 FStar.UInt64.uint_to_t
;                                                                                                                                   (
;                                                                                                                                     FStar.UInt64.v
;                                                                                                                                       start
;                                                                                                                                      +
;                                                                                                                                     (
;                                                                                                                                       FStar.UInt64.v
;                                                                                                                                         (
;                                                                                                                                           Pulse.Spec.GC.Object.getWosize
;                                                                                                                                             (
;                                                                                                                                               Pulse.Spec.GC.Heap.read_word
;                                                                                                                                                 g
;                                                                                                                                                 start
; 
;                                                                                                                                             )
; 
;                                                                                                                                         )
;                                                                                                                                        +
;                                                                                                                                       1
;                                                                                                                                     ) *
;                                                                                                                                     8
;                                                                                                                                   )
; 
;                                                                                                                               )
;                                                                                                                               g
; 
;                                                                                                                           )
; 
;                                                                                                                       )
;                                                                                                                      /\
;                                                                                                                     (
;                                                                                                                       forall
;                                                                                                                         (pure_result:
;                                                                                                                         Prims.unit)
;                                                                                                                       .
;                                                                                                                         Pulse.Spec.GC.Graph.is_vertex_set
;                                                                                                                           (
;                                                                                                                             FStar.Seq.Base.cons
;                                                                                                                               (
;                                                                                                                                 Pulse.Spec.GC.Fields.obj_address
;                                                                                                                                   start
; 
;                                                                                                                               )
;                                                                                                                               (
;                                                                                                                                 Pulse.Spec.GC.Fields.objects
;                                                                                                                                   (
;                                                                                                                                     FStar.UInt64.uint_to_t
;                                                                                                                                       (
;                                                                                                                                         FStar.UInt64.v
;                                                                                                                                           start
;                                                                                                                                          +
;                                                                                                                                         (
;                                                                                                                                           FStar.UInt64.v
;                                                                                                                                             (
;                                                                                                                                               Pulse.Spec.GC.Object.getWosize
;                                                                                                                                                 (
;                                                                                                                                                   Pulse.Spec.GC.Heap.read_word
;                                                                                                                                                     g
;                                                                                                                                                     start
; 
;                                                                                                                                                 )
; 
;                                                                                                                                             )
;                                                                                                                                            +
;                                                                                                                                           1
;                                                                                                                                         ) *
;                                                                                                                                         8
;                                                                                                                                       )
; 
;                                                                                                                                   )
;                                                                                                                                   g
; 
;                                                                                                                               )
; 
;                                                                                                                           )
;                                                                                                                          ==>
;                                                                                                                         k
;                                                                                                                           pure_result
; 
;                                                                                                                     )
;                                                                                                                 )
;                                                                                                             )
;                                                                                                         )
;                                                                                                     )
;                                                                                                 ))))
;                                                                                 ))))))))))))))))))))
;       ))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec objects_no_duplicates`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   ;; def=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post U_zero Prims.unit))
       ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
       (forall ((@x1 Term))
        (! (implies
          (and
           (or label_1 (HasType @x1 Prims.unit))
           ;; def=Pulse.Spec.GC.GraphBridge.fst(112,19-112,50); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
           (or
            label_2
            ;; def=Pulse.Spec.GC.GraphBridge.fst(112,19-112,50); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
            (BoxBool_proj_0
             (Pulse.Spec.GC.Graph.is_vertex_set
              (Pulse.Spec.GC.Fields.objects
               x_c39bed69b0e6a97dd42e9a16413dbcb1_0
               x_e246fc25c9201731c203dc9e18738560_1)))))
          ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
          (Valid
           ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
           (ApplyTT @x0 @x1)))
         :pattern
          (;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
           (Valid
            ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
            (ApplyTT @x0 @x1)))
         :qid @query.1)))
      ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post U_zero Prims.unit))
          ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
          (forall ((@x2 Term))
           (! (implies
             ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
             (Valid
              ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
              (ApplyTT @x0 @x2))
             ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
             (Valid
              ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
              (ApplyTT @x1 @x2)))
            :weight 0
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.3)))
         ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
         (and
          (implies
           ;; def=Pulse.Spec.GC.GraphBridge.fst(114,7-114,38); use=Pulse.Spec.GC.GraphBridge.fst(114,7-114,38)
           (=
            (Prims.op_GreaterThanOrEqual
             (Prims.op_Addition (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0) (BoxInt 8))
             (FStar.Seq.Base.length
              U_zero
              (FStar.UInt8.t Dummy_value)
              x_e246fc25c9201731c203dc9e18738560_1))
            (BoxBool true))
           ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(115,6-115,25)
           (forall ((@x2 Term))
            (! (implies
              (and
               (HasType @x2 Prims.unit)
               ;; def=Pulse.Spec.GC.Graph.fst(71,35-71,60); use=Pulse.Spec.GC.GraphBridge.fst(115,6-115,25)
               (BoxBool_proj_0
                (Pulse.Spec.GC.Graph.is_vertex_set
                 (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.vertex_id))))
              ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(115,6-115,25)
              (Valid
               ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(115,6-115,25)
               (ApplyTT @x1 @x2)))
             :qid @query.4)))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
           (not
            ;; def=Pulse.Spec.GC.GraphBridge.fst(114,7-114,38); use=Pulse.Spec.GC.GraphBridge.fst(114,7-114,38)
            (=
             (Prims.op_GreaterThanOrEqual
              (Prims.op_Addition (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0) (BoxInt 8))
              (FStar.Seq.Base.length
               U_zero
               (FStar.UInt8.t Dummy_value)
               x_e246fc25c9201731c203dc9e18738560_1))
             (BoxBool true)))
           ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
           (forall ((@x2 Term))
            (! (implies
              (and
               (HasType @x2 Prims.bool)
               ;; def=Pulse.Spec.GC.GraphBridge.fst(114,7-151,9); use=Pulse.Spec.GC.GraphBridge.fst(114,7-151,9)
               (=
                (Prims.op_GreaterThanOrEqual
                 (Prims.op_Addition (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0) (BoxInt 8))
                 (FStar.Seq.Base.length
                  U_zero
                  (FStar.UInt8.t Dummy_value)
                  x_e246fc25c9201731c203dc9e18738560_1))
                @x2))
              ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
              (forall ((@x3 Term))
               (! (implies
                 (and
                  (HasType @x3 (Prims.pure_post U_zero Prims.unit))
                  ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                  (forall ((@x4 Term))
                   (! (implies
                     ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                     (Valid
                      ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                      (ApplyTT @x1 @x4))
                     ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                     (Valid
                      ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                      (ApplyTT @x3 @x4)))
                    :weight 0
                    :pattern ((ApplyTT @x3 @x4))
                    :qid @query.7)))
                 ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                 (and
                  (implies
                   ;; def=Pulse.Spec.GC.GraphBridge.fst(122,9-122,67); use=Pulse.Spec.GC.GraphBridge.fst(122,9-122,67)
                   (=
                    (Prims.op_BarBar
                     (Prims.op_GreaterThan
                      (Prims.op_Addition
                       (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                       (Prims.op_Multiply
                        (Prims.op_Addition
                         (FStar.UInt64.v
                          (Pulse.Spec.GC.Object.getWosize
                           (Pulse.Spec.GC.Heap.read_word
                            x_e246fc25c9201731c203dc9e18738560_1
                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                         (BoxInt 1))
                        (BoxInt 8)))
                      (FStar.Seq.Base.length
                       U_zero
                       (FStar.UInt8.t Dummy_value)
                       x_e246fc25c9201731c203dc9e18738560_1))
                     (Prims.op_GreaterThanOrEqual
                      (Prims.op_Addition
                       (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                       (Prims.op_Multiply
                        (Prims.op_Addition
                         (FStar.UInt64.v
                          (Pulse.Spec.GC.Object.getWosize
                           (Pulse.Spec.GC.Heap.read_word
                            x_e246fc25c9201731c203dc9e18738560_1
                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                         (BoxInt 1))
                        (BoxInt 8)))
                      (Prims.pow2 (BoxInt 64))))
                    (BoxBool true))
                   ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(123,8-123,27)
                   (forall ((@x4 Term))
                    (! (implies
                      (and
                       (HasType @x4 Prims.unit)
                       ;; def=Pulse.Spec.GC.Graph.fst(71,35-71,60); use=Pulse.Spec.GC.GraphBridge.fst(123,8-123,27)
                       (BoxBool_proj_0
                        (Pulse.Spec.GC.Graph.is_vertex_set
                         (FStar.Seq.Base.empty U_zero Pulse.Spec.GC.Graph.vertex_id))))
                      ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(123,8-123,27)
                      (Valid
                       ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(123,8-123,27)
                       (ApplyTT @x3 @x4)))
                     :qid @query.8)))
                  (implies
                   ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                   (not
                    ;; def=Pulse.Spec.GC.GraphBridge.fst(122,9-122,67); use=Pulse.Spec.GC.GraphBridge.fst(122,9-122,67)
                    (=
                     (Prims.op_BarBar
                      (Prims.op_GreaterThan
                       (Prims.op_Addition
                        (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                        (Prims.op_Multiply
                         (Prims.op_Addition
                          (FStar.UInt64.v
                           (Pulse.Spec.GC.Object.getWosize
                            (Pulse.Spec.GC.Heap.read_word
                             x_e246fc25c9201731c203dc9e18738560_1
                             x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                          (BoxInt 1))
                         (BoxInt 8)))
                       (FStar.Seq.Base.length
                        U_zero
                        (FStar.UInt8.t Dummy_value)
                        x_e246fc25c9201731c203dc9e18738560_1))
                      (Prims.op_GreaterThanOrEqual
                       (Prims.op_Addition
                        (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                        (Prims.op_Multiply
                         (Prims.op_Addition
                          (FStar.UInt64.v
                           (Pulse.Spec.GC.Object.getWosize
                            (Pulse.Spec.GC.Heap.read_word
                             x_e246fc25c9201731c203dc9e18738560_1
                             x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                          (BoxInt 1))
                         (BoxInt 8)))
                       (Prims.pow2 (BoxInt 64))))
                     (BoxBool true)))
                   ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                   (forall ((@x4 Term))
                    (! (implies
                      (and
                       (HasType @x4 Prims.bool)
                       ;; def=Pulse.Spec.GC.GraphBridge.fst(122,9-150,11); use=Pulse.Spec.GC.GraphBridge.fst(122,9-150,11)
                       (=
                        (Prims.op_BarBar
                         (Prims.op_GreaterThan
                          (Prims.op_Addition
                           (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                           (Prims.op_Multiply
                            (Prims.op_Addition
                             (FStar.UInt64.v
                              (Pulse.Spec.GC.Object.getWosize
                               (Pulse.Spec.GC.Heap.read_word
                                x_e246fc25c9201731c203dc9e18738560_1
                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                             (BoxInt 1))
                            (BoxInt 8)))
                          (FStar.Seq.Base.length
                           U_zero
                           (FStar.UInt8.t Dummy_value)
                           x_e246fc25c9201731c203dc9e18738560_1))
                         (Prims.op_GreaterThanOrEqual
                          (Prims.op_Addition
                           (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                           (Prims.op_Multiply
                            (Prims.op_Addition
                             (FStar.UInt64.v
                              (Pulse.Spec.GC.Object.getWosize
                               (Pulse.Spec.GC.Heap.read_word
                                x_e246fc25c9201731c203dc9e18738560_1
                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                             (BoxInt 1))
                            (BoxInt 8)))
                          (Prims.pow2 (BoxInt 64))))
                        @x4))
                      ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                      (and
                       (implies
                        ;; def=Prims.fst(685,18-685,23); use=Pulse.Spec.GC.GraphBridge.fst(126,57-126,64)
                        (> (BoxInt_proj_0 (Prims.pow2 (BoxInt 64))) (BoxInt_proj_0 (BoxInt 0)))
                        ;; def=Prims.fst(688,22-688,28); use=Pulse.Spec.GC.GraphBridge.fst(126,57-126,64)
                        (or
                         label_3
                         ;; def=Prims.fst(688,22-688,28); use=Pulse.Spec.GC.GraphBridge.fst(126,57-126,64)
                         (not (= (Prims.pow2 (BoxInt 64)) (BoxInt 0)))))
                       ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                       (forall ((@x5 Term))
                        (! (implies
                          (and
                           (HasType @x5 Prims.nonzero)
                           ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                           (= @x5 (Prims.pow2 (BoxInt 64))))
                          ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                          (forall ((@x6 Term))
                           (! (implies
                             (and
                              (HasType @x6 Prims.int)
                              ;; def=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                              (=
                               (Prims.op_Modulus
                                (Prims.op_Addition
                                 (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                 (BoxInt 8))
                                (Prims.pow2 (BoxInt 64)))
                               @x6))
                             ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                             (forall ((@x7 Term))
                              (! (implies
                                (and
                                 (HasType @x7 Prims.bool)
                                 ;; def=Prims.fst(188,10-188,11); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                 (=
                                  (Prims.op_Equality
                                   Prims.int
                                   (FStar.UInt64.v
                                    (Pulse.Spec.GC.Fields.obj_address
                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                   (Prims.op_Modulus
                                    (Prims.op_Addition
                                     (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                     (BoxInt 8))
                                    (Prims.pow2 (BoxInt 64))))
                                  @x7))
                                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                (forall ((@x8 Term))
                                 (! (implies
                                   (and
                                    (HasType @x8 Prims.logical)
                                    ;; def=Prims.fst(674,13-674,14); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                    (=
                                     (Prims.b2t
                                      (Prims.op_Equality
                                       Prims.int
                                       (FStar.UInt64.v
                                        (Pulse.Spec.GC.Fields.obj_address
                                         x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                       (Prims.op_Modulus
                                        (Prims.op_Addition
                                         (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                         (BoxInt 8))
                                        (Prims.pow2 (BoxInt 64)))))
                                     @x8))
                                   ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(126,8-126,14)
                                   (and
                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(126,15-126,65); use=Pulse.Spec.GC.GraphBridge.fst(126,8-126,14)
                                    (or
                                     label_4
                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(126,15-126,65); use=Pulse.Spec.GC.GraphBridge.fst(126,8-126,14)
                                     (=
                                      (FStar.UInt64.v
                                       (Pulse.Spec.GC.Fields.obj_address
                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                      (Prims.op_Modulus
                                       (Prims.op_Addition
                                        (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                        (BoxInt 8))
                                       (Prims.pow2 (BoxInt 64)))))
                                    ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(126,8-126,14)
                                    (forall ((@x9 Term))
                                     (! (implies
                                       (and
                                        (HasType @x9 Prims.unit)
                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(126,15-126,65); use=Pulse.Spec.GC.GraphBridge.fst(126,8-126,14)
                                        (=
                                         (FStar.UInt64.v
                                          (Pulse.Spec.GC.Fields.obj_address
                                           x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                         (Prims.op_Modulus
                                          (Prims.op_Addition
                                           (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                           (BoxInt 8))
                                          (Prims.pow2 (BoxInt 64)))))
                                       ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(127,8-127,14)
                                       (and
                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(127,15-127,44); use=Pulse.Spec.GC.GraphBridge.fst(127,8-127,14)
                                        (or
                                         label_5
                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(127,15-127,44); use=Pulse.Spec.GC.GraphBridge.fst(127,8-127,14)
                                         (<
                                          (BoxInt_proj_0
                                           (Prims.op_Addition
                                            (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                            (BoxInt 8)))
                                          (BoxInt_proj_0 (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                        ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(127,8-127,14)
                                        (forall ((@x10 Term))
                                         (! (implies
                                           (and
                                            (HasType @x10 Prims.unit)
                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(127,15-127,44); use=Pulse.Spec.GC.GraphBridge.fst(127,8-127,14)
                                            (<
                                             (BoxInt_proj_0
                                              (Prims.op_Addition
                                               (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                               (BoxInt 8)))
                                             (BoxInt_proj_0
                                              (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                           ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(128,8-128,14)
                                           (and
                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(128,15-128,42); use=Pulse.Spec.GC.GraphBridge.fst(128,8-128,14)
                                            (or
                                             label_6
                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(128,15-128,42); use=Pulse.Spec.GC.GraphBridge.fst(128,8-128,14)
                                             (<
                                              (BoxInt_proj_0
                                               (Prims.op_Addition
                                                (FStar.UInt64.v x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                (BoxInt 8)))
                                              (BoxInt_proj_0 (Prims.pow2 (BoxInt 64)))))
                                            ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(128,8-128,14)
                                            (forall ((@x11 Term))
                                             (! (implies
                                               (and
                                                (HasType @x11 Prims.unit)
                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(128,15-128,42); use=Pulse.Spec.GC.GraphBridge.fst(128,8-128,14)
                                                (<
                                                 (BoxInt_proj_0
                                                  (Prims.op_Addition
                                                   (FStar.UInt64.v
                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                   (BoxInt 8)))
                                                 (BoxInt_proj_0 (Prims.pow2 (BoxInt 64)))))
                                               ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(129,8-129,14)
                                               (and
                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(129,15-129,53); use=Pulse.Spec.GC.GraphBridge.fst(129,8-129,14)
                                                (or
                                                 label_7
                                                 ;; def=Pulse.Spec.GC.GraphBridge.fst(129,15-129,53); use=Pulse.Spec.GC.GraphBridge.fst(129,8-129,14)
                                                 (=
                                                  (FStar.UInt64.v
                                                   (Pulse.Spec.GC.Fields.obj_address
                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                                  (Prims.op_Addition
                                                   (FStar.UInt64.v
                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                   (BoxInt 8))))
                                                ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(129,8-129,14)
                                                (forall ((@x12 Term))
                                                 (! (implies
                                                   (and
                                                    (HasType @x12 Prims.unit)
                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(129,15-129,53); use=Pulse.Spec.GC.GraphBridge.fst(129,8-129,14)
                                                    (=
                                                     (FStar.UInt64.v
                                                      (Pulse.Spec.GC.Fields.obj_address
                                                       x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                                     (Prims.op_Addition
                                                      (FStar.UInt64.v
                                                       x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                      (BoxInt 8))))
                                                   ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(130,8-130,14)
                                                   (and
                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(130,15-130,47); use=Pulse.Spec.GC.GraphBridge.fst(130,8-130,14)
                                                    (or
                                                     label_8
                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(130,15-130,47); use=Pulse.Spec.GC.GraphBridge.fst(130,8-130,14)
                                                     (<
                                                      (BoxInt_proj_0
                                                       (FStar.UInt64.v
                                                        (Pulse.Spec.GC.Fields.obj_address
                                                         x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                      (BoxInt_proj_0
                                                       (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                                    ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(130,8-130,14)
                                                    (forall ((@x13 Term))
                                                     (! (implies
                                                       (and
                                                        (HasType @x13 Prims.unit)
                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(130,15-130,47); use=Pulse.Spec.GC.GraphBridge.fst(130,8-130,14)
                                                        (<
                                                         (BoxInt_proj_0
                                                          (FStar.UInt64.v
                                                           (Pulse.Spec.GC.Fields.obj_address
                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                         (BoxInt_proj_0
                                                          (Pulse.Spec.GC.Base.heap_size Dummy_value))))
                                                       ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(131,8-131,14)
                                                       (and
                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(131,15-131,43); use=Pulse.Spec.GC.GraphBridge.fst(131,8-131,14)
                                                        (or
                                                         label_9
                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(131,15-131,43); use=Pulse.Spec.GC.GraphBridge.fst(131,8-131,14)
                                                         (=
                                                          (Prims.op_Modulus
                                                           (FStar.UInt64.v
                                                            (Pulse.Spec.GC.Fields.obj_address
                                                             x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                                           (BoxInt 8))
                                                          (BoxInt 0)))
                                                        ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(131,8-131,14)
                                                        (forall ((@x14 Term))
                                                         (! (implies
                                                           (and
                                                            (HasType @x14 Prims.unit)
                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(131,15-131,43); use=Pulse.Spec.GC.GraphBridge.fst(131,8-131,14)
                                                            (=
                                                             (Prims.op_Modulus
                                                              (FStar.UInt64.v
                                                               (Pulse.Spec.GC.Fields.obj_address
                                                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                                              (BoxInt 8))
                                                             (BoxInt 0)))
                                                           ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                           (and
                                                            ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                            (or
                                                             label_10
                                                             ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                             (>=
                                                              (BoxInt_proj_0
                                                               (FStar.UInt64.v
                                                                (Pulse.Spec.GC.Fields.obj_address
                                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                              (BoxInt_proj_0 (BoxInt 0))))
                                                            ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                            (or
                                                             label_11
                                                             ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                             (<
                                                              (BoxInt_proj_0
                                                               (FStar.UInt64.v
                                                                (Pulse.Spec.GC.Fields.obj_address
                                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                              (BoxInt_proj_0
                                                               (Pulse.Spec.GC.Base.heap_size
                                                                Dummy_value))))
                                                            ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                            (or
                                                             label_12
                                                             ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(132,33-132,45)
                                                             (=
                                                              (Prims.op_Modulus
                                                               (FStar.UInt64.v
                                                                (Pulse.Spec.GC.Fields.obj_address
                                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_0))
                                                               (FStar.UInt64.v
                                                                (Pulse.Spec.GC.Base.mword
                                                                 Dummy_value)))
                                                              (BoxInt 0)))
                                                            ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                            (forall ((@x15 Term))
                                                             (! (implies
                                                               (and
                                                                (HasType
                                                                 @x15
                                                                 (FStar.UInt64.t Dummy_value))
                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(119,10-132,20); use=Pulse.Spec.GC.GraphBridge.fst(132,12-132,45)
                                                                (=
                                                                 (Pulse.Spec.GC.Fields.obj_address
                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                 @x15))
                                                               ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                               (forall ((@x16 Term))
                                                                (! (implies
                                                                  (and
                                                                   (HasType
                                                                    @x16
                                                                    (Prims.pure_post
                                                                     U_zero
                                                                     Prims.unit))
                                                                   ;; def=Prims.fst(410,2-410,97); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                   (forall ((@x17 Term))
                                                                    (! (implies
                                                                      ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                      (Valid
                                                                       ;; def=Prims.fst(410,73-410,79); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                       (ApplyTT @x3 @x17))
                                                                      ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                      (Valid
                                                                       ;; def=Prims.fst(410,84-410,87); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                       (ApplyTT @x16 @x17)))
                                                                     :weight 0
                                                                     :pattern ((ApplyTT @x16 @x17))
                                                                     :qid @query.22)))
                                                                  ;; def=Prims.fst(397,2-397,39); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                  (and
                                                                   (implies
                                                                    ;; def=Pulse.Spec.GC.GraphBridge.fst(135,11-135,38); use=Pulse.Spec.GC.GraphBridge.fst(135,11-135,38)
                                                                    (=
                                                                     (Prims.op_GreaterThanOrEqual
                                                                      (Prims.op_Addition
                                                                       (FStar.UInt64.v
                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                       (Prims.op_Multiply
                                                                        (Prims.op_Addition
                                                                         (FStar.UInt64.v
                                                                          (Pulse.Spec.GC.Object.getWosize
                                                                           (Pulse.Spec.GC.Heap.read_word
                                                                            x_e246fc25c9201731c203dc9e18738560_1
                                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                         (BoxInt 1))
                                                                        (BoxInt 8)))
                                                                      (Pulse.Spec.GC.Base.heap_size
                                                                       Dummy_value))
                                                                     (BoxBool true))
                                                                    ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(136,10-136,33)
                                                                    (forall ((@x17 Term))
                                                                     (! (implies
                                                                       (and
                                                                        (HasType @x17 Prims.unit)
                                                                        ;; def=Pulse.Spec.GC.Graph.fst(75,10-75,42); use=Pulse.Spec.GC.GraphBridge.fst(136,10-136,33)
                                                                        (BoxBool_proj_0
                                                                         (Pulse.Spec.GC.Graph.is_vertex_set
                                                                          (FStar.Seq.Base.create
                                                                           U_zero
                                                                           Pulse.Spec.GC.Graph.vertex_id
                                                                           (BoxInt 1)
                                                                           (Pulse.Spec.GC.Fields.obj_address
                                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))))
                                                                       ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(136,10-136,33)
                                                                       (Valid
                                                                        ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(136,10-136,33)
                                                                        (ApplyTT @x16 @x17)))
                                                                      :qid @query.23)))
                                                                   (implies
                                                                    ;; def=Prims.fst(397,19-397,21); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                    (not
                                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(135,11-135,38); use=Pulse.Spec.GC.GraphBridge.fst(135,11-135,38)
                                                                     (=
                                                                      (Prims.op_GreaterThanOrEqual
                                                                       (Prims.op_Addition
                                                                        (FStar.UInt64.v
                                                                         x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                        (Prims.op_Multiply
                                                                         (Prims.op_Addition
                                                                          (FStar.UInt64.v
                                                                           (Pulse.Spec.GC.Object.getWosize
                                                                            (Pulse.Spec.GC.Heap.read_word
                                                                             x_e246fc25c9201731c203dc9e18738560_1
                                                                             x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                          (BoxInt 1))
                                                                         (BoxInt 8)))
                                                                       (Pulse.Spec.GC.Base.heap_size
                                                                        Dummy_value))
                                                                      (BoxBool true)))
                                                                    ;; def=Prims.fst(421,99-421,120); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                    (forall ((@x17 Term))
                                                                     (! (implies
                                                                       (and
                                                                        (HasType @x17 Prims.bool)
                                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(135,11-149,42); use=Pulse.Spec.GC.GraphBridge.fst(135,11-149,42)
                                                                        (=
                                                                         (Prims.op_GreaterThanOrEqual
                                                                          (Prims.op_Addition
                                                                           (FStar.UInt64.v
                                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                           (Prims.op_Multiply
                                                                            (Prims.op_Addition
                                                                             (FStar.UInt64.v
                                                                              (Pulse.Spec.GC.Object.getWosize
                                                                               (Pulse.Spec.GC.Heap.read_word
                                                                                x_e246fc25c9201731c203dc9e18738560_1
                                                                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                             (BoxInt 1))
                                                                            (BoxInt 8)))
                                                                          (Pulse.Spec.GC.Base.heap_size
                                                                           Dummy_value))
                                                                         @x17))
                                                                       ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(138,10-138,16)
                                                                       (and
                                                                        ;; def=Pulse.Spec.GC.GraphBridge.fst(138,17-138,45); use=Pulse.Spec.GC.GraphBridge.fst(138,10-138,16)
                                                                        (or
                                                                         label_13
                                                                         ;; def=Pulse.Spec.GC.GraphBridge.fst(138,17-138,45); use=Pulse.Spec.GC.GraphBridge.fst(138,10-138,16)
                                                                         (<
                                                                          (BoxInt_proj_0
                                                                           (Prims.op_Addition
                                                                            (FStar.UInt64.v
                                                                             x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                            (Prims.op_Multiply
                                                                             (Prims.op_Addition
                                                                              (FStar.UInt64.v
                                                                               (Pulse.Spec.GC.Object.getWosize
                                                                                (Pulse.Spec.GC.Heap.read_word
                                                                                 x_e246fc25c9201731c203dc9e18738560_1
                                                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                              (BoxInt 1))
                                                                             (BoxInt 8))))
                                                                          (BoxInt_proj_0
                                                                           (Pulse.Spec.GC.Base.heap_size
                                                                            Dummy_value))))
                                                                        ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(138,10-138,16)
                                                                        (forall ((@x18 Term))
                                                                         (! (implies
                                                                           (and
                                                                            (HasType @x18 Prims.unit)
                                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(138,17-138,45); use=Pulse.Spec.GC.GraphBridge.fst(138,10-138,16)
                                                                            (<
                                                                             (BoxInt_proj_0
                                                                              (Prims.op_Addition
                                                                               (FStar.UInt64.v
                                                                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                               (Prims.op_Multiply
                                                                                (Prims.op_Addition
                                                                                 (FStar.UInt64.v
                                                                                  (Pulse.Spec.GC.Object.getWosize
                                                                                   (Pulse.Spec.GC.Heap.read_word
                                                                                    x_e246fc25c9201731c203dc9e18738560_1
                                                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                 (BoxInt 1))
                                                                                (BoxInt 8))))
                                                                             (BoxInt_proj_0
                                                                              (Pulse.Spec.GC.Base.heap_size
                                                                               Dummy_value))))
                                                                           ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(139,10-139,16)
                                                                           (and
                                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(139,17-139,41); use=Pulse.Spec.GC.GraphBridge.fst(139,10-139,16)
                                                                            (or
                                                                             label_14
                                                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(139,17-139,41); use=Pulse.Spec.GC.GraphBridge.fst(139,10-139,16)
                                                                             (=
                                                                              (Prims.op_Modulus
                                                                               (Prims.op_Addition
                                                                                (FStar.UInt64.v
                                                                                 x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                (Prims.op_Multiply
                                                                                 (Prims.op_Addition
                                                                                  (FStar.UInt64.v
                                                                                   (Pulse.Spec.GC.Object.getWosize
                                                                                    (Pulse.Spec.GC.Heap.read_word
                                                                                     x_e246fc25c9201731c203dc9e18738560_1
                                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                  (BoxInt 1))
                                                                                 (BoxInt 8)))
                                                                               (BoxInt 8))
                                                                              (BoxInt 0)))
                                                                            ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(139,10-139,16)
                                                                            (forall ((@x19 Term))
                                                                             (! (implies
                                                                               (and
                                                                                (HasType
                                                                                 @x19
                                                                                 Prims.unit)
                                                                                ;; def=Pulse.Spec.GC.GraphBridge.fst(139,17-139,41); use=Pulse.Spec.GC.GraphBridge.fst(139,10-139,16)
                                                                                (=
                                                                                 (Prims.op_Modulus
                                                                                  (Prims.op_Addition
                                                                                   (FStar.UInt64.v
                                                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                   (Prims.op_Multiply
                                                                                    (Prims.op_Addition
                                                                                     (FStar.UInt64.v
                                                                                      (Pulse.Spec.GC.Object.getWosize
                                                                                       (Pulse.Spec.GC.Heap.read_word
                                                                                        x_e246fc25c9201731c203dc9e18738560_1
                                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                     (BoxInt 1))
                                                                                    (BoxInt 8)))
                                                                                  (BoxInt 8))
                                                                                 (BoxInt 0)))
                                                                               ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                               (and
                                                                                ;; def=FStar.UInt.fsti(54,28-54,36); use=Pulse.Spec.GC.GraphBridge.fst(140,51-140,65)
                                                                                (or
                                                                                 label_15
                                                                                 ;; def=FStar.UInt.fsti(54,28-54,36); use=Pulse.Spec.GC.GraphBridge.fst(140,51-140,65)
                                                                                 (Valid
                                                                                  ;; def=FStar.UInt.fsti(54,28-54,36); use=Pulse.Spec.GC.GraphBridge.fst(140,51-140,65)
                                                                                  (FStar.UInt.size
                                                                                   (Prims.op_Addition
                                                                                    (FStar.UInt64.v
                                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                    (Prims.op_Multiply
                                                                                     (Prims.op_Addition
                                                                                      (FStar.UInt64.v
                                                                                       (Pulse.Spec.GC.Object.getWosize
                                                                                        (Pulse.Spec.GC.Heap.read_word
                                                                                         x_e246fc25c9201731c203dc9e18738560_1
                                                                                         x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                      (BoxInt 1))
                                                                                     (BoxInt 8)))
                                                                                   (BoxInt 64))))
                                                                                ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                (forall
                                                                                  ((@x20 Term))
                                                                                 (! (implies
                                                                                   (and
                                                                                    (HasType
                                                                                     @x20
                                                                                     Prims.int)
                                                                                    ;; def=FStar.UInt64.fsti(58,15-58,16); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                    (=
                                                                                     (Prims.op_Addition
                                                                                      (FStar.UInt64.v
                                                                                       x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                      (Prims.op_Multiply
                                                                                       (Prims.op_Addition
                                                                                        (FStar.UInt64.v
                                                                                         (Pulse.Spec.GC.Object.getWosize
                                                                                          (Pulse.Spec.GC.Heap.read_word
                                                                                           x_e246fc25c9201731c203dc9e18738560_1
                                                                                           x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                        (BoxInt 1))
                                                                                       (BoxInt 8)))
                                                                                     @x20))
                                                                                   ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(140,41-140,50)
                                                                                   (forall
                                                                                     ((@x21 Term))
                                                                                    (! (implies
                                                                                      (and
                                                                                       (HasType
                                                                                        @x21
                                                                                        (FStar.UInt64.t
                                                                                         Dummy_value))
                                                                                       ;; def=FStar.UInt64.fsti(60,21-60,28); use=Pulse.Spec.GC.GraphBridge.fst(140,41-140,50)
                                                                                       (=
                                                                                        (FStar.UInt64.v
                                                                                         @x21)
                                                                                        (Prims.op_Addition
                                                                                         (FStar.UInt64.v
                                                                                          x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                         (Prims.op_Multiply
                                                                                          (Prims.op_Addition
                                                                                           (FStar.UInt64.v
                                                                                            (Pulse.Spec.GC.Object.getWosize
                                                                                             (Pulse.Spec.GC.Heap.read_word
                                                                                              x_e246fc25c9201731c203dc9e18738560_1
                                                                                              x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                           (BoxInt 1))
                                                                                          (BoxInt 8))))
                                                                                       ;; def=Pulse.Spec.GC.GraphBridge.fst(140,27-140,65); use=Pulse.Spec.GC.GraphBridge.fst(140,27-140,65)
                                                                                       (=
                                                                                        (FStar.UInt64.uint_to_t
                                                                                         (Prims.op_Addition
                                                                                          (FStar.UInt64.v
                                                                                           x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                          (Prims.op_Multiply
                                                                                           (Prims.op_Addition
                                                                                            (FStar.UInt64.v
                                                                                             (Pulse.Spec.GC.Object.getWosize
                                                                                              (Pulse.Spec.GC.Heap.read_word
                                                                                               x_e246fc25c9201731c203dc9e18738560_1
                                                                                               x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                            (BoxInt
                                                                                             1))
                                                                                           (BoxInt 8))))
                                                                                        @x21))
                                                                                      ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                      (and
                                                                                       ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                       (or
                                                                                        label_16
                                                                                        ;; def=Pulse.Spec.GC.Base.fsti(44,2-44,14); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                        (>=
                                                                                         (BoxInt_proj_0
                                                                                          (FStar.UInt64.v
                                                                                           (FStar.UInt64.uint_to_t
                                                                                            (Prims.op_Addition
                                                                                             (FStar.UInt64.v
                                                                                              x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                             (Prims.op_Multiply
                                                                                              (Prims.op_Addition
                                                                                               (FStar.UInt64.v
                                                                                                (Pulse.Spec.GC.Object.getWosize
                                                                                                 (Pulse.Spec.GC.Heap.read_word
                                                                                                  x_e246fc25c9201731c203dc9e18738560_1
                                                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                               (BoxInt
                                                                                                1))
                                                                                              (BoxInt
                                                                                               8))))))
                                                                                         (BoxInt_proj_0
                                                                                          (BoxInt 0))))
                                                                                       ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                       (or
                                                                                        label_17
                                                                                        ;; def=Pulse.Spec.GC.Base.fsti(45,2-45,21); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                        (<
                                                                                         (BoxInt_proj_0
                                                                                          (FStar.UInt64.v
                                                                                           (FStar.UInt64.uint_to_t
                                                                                            (Prims.op_Addition
                                                                                             (FStar.UInt64.v
                                                                                              x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                             (Prims.op_Multiply
                                                                                              (Prims.op_Addition
                                                                                               (FStar.UInt64.v
                                                                                                (Pulse.Spec.GC.Object.getWosize
                                                                                                 (Pulse.Spec.GC.Heap.read_word
                                                                                                  x_e246fc25c9201731c203dc9e18738560_1
                                                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                               (BoxInt
                                                                                                1))
                                                                                              (BoxInt
                                                                                               8))))))
                                                                                         (BoxInt_proj_0
                                                                                          (Pulse.Spec.GC.Base.heap_size
                                                                                           Dummy_value))))
                                                                                       ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                       (or
                                                                                        label_18
                                                                                        ;; def=Pulse.Spec.GC.Base.fsti(46,2-46,28); use=Pulse.Spec.GC.GraphBridge.fst(140,37-140,65)
                                                                                        (=
                                                                                         (Prims.op_Modulus
                                                                                          (FStar.UInt64.v
                                                                                           (FStar.UInt64.uint_to_t
                                                                                            (Prims.op_Addition
                                                                                             (FStar.UInt64.v
                                                                                              x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                             (Prims.op_Multiply
                                                                                              (Prims.op_Addition
                                                                                               (FStar.UInt64.v
                                                                                                (Pulse.Spec.GC.Object.getWosize
                                                                                                 (Pulse.Spec.GC.Heap.read_word
                                                                                                  x_e246fc25c9201731c203dc9e18738560_1
                                                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                               (BoxInt
                                                                                                1))
                                                                                              (BoxInt
                                                                                               8)))))
                                                                                          (FStar.UInt64.v
                                                                                           (Pulse.Spec.GC.Base.mword
                                                                                            Dummy_value)))
                                                                                         (BoxInt 0)))
                                                                                       ;; def=Prims.fst(364,2-364,58); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                       (forall
                                                                                         ((@x22 Term))
                                                                                        (! (implies
                                                                                          (and
                                                                                           (HasType
                                                                                            @x22
                                                                                            Pulse.Spec.GC.Base.hp_addr)
                                                                                           ;; def=Prims.fst(364,26-364,41); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                           (=
                                                                                            @x22
                                                                                            (FStar.UInt64.uint_to_t
                                                                                             (Prims.op_Addition
                                                                                              (FStar.UInt64.v
                                                                                               x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                              (Prims.op_Multiply
                                                                                               (Prims.op_Addition
                                                                                                (FStar.UInt64.v
                                                                                                 (Pulse.Spec.GC.Object.getWosize
                                                                                                  (Pulse.Spec.GC.Heap.read_word
                                                                                                   x_e246fc25c9201731c203dc9e18738560_1
                                                                                                   x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                (BoxInt
                                                                                                 1))
                                                                                               (BoxInt
                                                                                                8)))))
                                                                                           ;; def=Pulse.Spec.GC.GraphBridge.fst(140,14-140,65); use=Pulse.Spec.GC.GraphBridge.fst(140,14-140,65)
                                                                                           (=
                                                                                            (FStar.UInt64.uint_to_t
                                                                                             (Prims.op_Addition
                                                                                              (FStar.UInt64.v
                                                                                               x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                              (Prims.op_Multiply
                                                                                               (Prims.op_Addition
                                                                                                (FStar.UInt64.v
                                                                                                 (Pulse.Spec.GC.Object.getWosize
                                                                                                  (Pulse.Spec.GC.Heap.read_word
                                                                                                   x_e246fc25c9201731c203dc9e18738560_1
                                                                                                   x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                (BoxInt
                                                                                                 1))
                                                                                               (BoxInt
                                                                                                8))))
                                                                                            @x22))
                                                                                          ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                          (and
                                                                                           ;; def=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7); use=Pulse.Spec.GC.GraphBridge.fst(142,43-142,44)
                                                                                           (or
                                                                                            label_19
                                                                                            ;; def=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7); use=Pulse.Spec.GC.GraphBridge.fst(142,43-142,44)
                                                                                            (Valid
                                                                                             ;; def=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7); use=Pulse.Spec.GC.GraphBridge.fst(142,43-142,44)
                                                                                             (Prims.precedes
                                                                                              U_zero
                                                                                              U_zero
                                                                                              Prims.int
                                                                                              Prims.int
                                                                                              (Prims.op_Subtraction
                                                                                               (FStar.Seq.Base.length
                                                                                                U_zero
                                                                                                (FStar.UInt8.t
                                                                                                 Dummy_value)
                                                                                                x_e246fc25c9201731c203dc9e18738560_1)
                                                                                               (FStar.UInt64.v
                                                                                                (FStar.UInt64.uint_to_t
                                                                                                 (Prims.op_Addition
                                                                                                  (FStar.UInt64.v
                                                                                                   x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                  (Prims.op_Multiply
                                                                                                   (Prims.op_Addition
                                                                                                    (FStar.UInt64.v
                                                                                                     (Pulse.Spec.GC.Object.getWosize
                                                                                                      (Pulse.Spec.GC.Heap.read_word
                                                                                                       x_e246fc25c9201731c203dc9e18738560_1
                                                                                                       x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                    (BoxInt
                                                                                                     1))
                                                                                                   (BoxInt
                                                                                                    8))))))
                                                                                              (Prims.op_Subtraction
                                                                                               (FStar.Seq.Base.length
                                                                                                U_zero
                                                                                                (FStar.UInt8.t
                                                                                                 Dummy_value)
                                                                                                x_e246fc25c9201731c203dc9e18738560_1)
                                                                                               (FStar.UInt64.v
                                                                                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))))
                                                                                           ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                           (forall
                                                                                             ((@x23
                                                                                               Term))
                                                                                            (! (implies
                                                                                              (and
                                                                                               (HasType
                                                                                                @x23
                                                                                                Pulse.Spec.GC.Base.heap)
                                                                                               ;; def=Pulse.Spec.GC.GraphBridge.fst(111,48-111,49); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                               (=
                                                                                                x_e246fc25c9201731c203dc9e18738560_1
                                                                                                @x23))
                                                                                              ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(142,10-142,31)
                                                                                              (forall
                                                                                                ((@x24
                                                                                                  Term))
                                                                                               (! (implies
                                                                                                 (and
                                                                                                  (HasType
                                                                                                   @x24
                                                                                                   Prims.unit)
                                                                                                  ;; def=Pulse.Spec.GC.GraphBridge.fst(112,19-112,50); use=Pulse.Spec.GC.GraphBridge.fst(142,10-142,31)
                                                                                                  (BoxBool_proj_0
                                                                                                   (Pulse.Spec.GC.Graph.is_vertex_set
                                                                                                    (Pulse.Spec.GC.Fields.objects
                                                                                                     (FStar.UInt64.uint_to_t
                                                                                                      (Prims.op_Addition
                                                                                                       (FStar.UInt64.v
                                                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                       (Prims.op_Multiply
                                                                                                        (Prims.op_Addition
                                                                                                         (FStar.UInt64.v
                                                                                                          (Pulse.Spec.GC.Object.getWosize
                                                                                                           (Pulse.Spec.GC.Heap.read_word
                                                                                                            x_e246fc25c9201731c203dc9e18738560_1
                                                                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                         (BoxInt
                                                                                                          1))
                                                                                                        (BoxInt
                                                                                                         8))))
                                                                                                     x_e246fc25c9201731c203dc9e18738560_1))))
                                                                                                 ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                                 (forall
                                                                                                   ((@x25
                                                                                                     Term))
                                                                                                  (! (implies
                                                                                                    (and
                                                                                                     (HasType
                                                                                                      @x25
                                                                                                      (FStar.Seq.Base.seq
                                                                                                       U_zero
                                                                                                       Pulse.Spec.GC.Base.hp_addr))
                                                                                                     ;; def=Pulse.Spec.GC.GraphBridge.fst(143,14-143,41); use=Pulse.Spec.GC.GraphBridge.fst(143,14-143,41)
                                                                                                     (=
                                                                                                      (Pulse.Spec.GC.Fields.objects
                                                                                                       (FStar.UInt64.uint_to_t
                                                                                                        (Prims.op_Addition
                                                                                                         (FStar.UInt64.v
                                                                                                          x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                         (Prims.op_Multiply
                                                                                                          (Prims.op_Addition
                                                                                                           (FStar.UInt64.v
                                                                                                            (Pulse.Spec.GC.Object.getWosize
                                                                                                             (Pulse.Spec.GC.Heap.read_word
                                                                                                              x_e246fc25c9201731c203dc9e18738560_1
                                                                                                              x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                           (BoxInt
                                                                                                            1))
                                                                                                          (BoxInt
                                                                                                           8))))
                                                                                                       x_e246fc25c9201731c203dc9e18738560_1)
                                                                                                      @x25))
                                                                                                    ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(145,10-145,34)
                                                                                                    (and
                                                                                                     ;; def=Pulse.Spec.GC.Fields.fst(191,20-191,51); use=Pulse.Spec.GC.GraphBridge.fst(145,10-145,34)
                                                                                                     (or
                                                                                                      label_20
                                                                                                      ;; def=Pulse.Spec.GC.Fields.fst(191,20-191,51); use=Pulse.Spec.GC.GraphBridge.fst(145,10-145,34)
                                                                                                      (<=
                                                                                                       (BoxInt_proj_0
                                                                                                        (Prims.op_Addition
                                                                                                         (FStar.UInt64.v
                                                                                                          x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                         (BoxInt
                                                                                                          8)))
                                                                                                       (BoxInt_proj_0
                                                                                                        (FStar.Seq.Base.length
                                                                                                         U_zero
                                                                                                         (FStar.UInt8.t
                                                                                                          Dummy_value)
                                                                                                         x_e246fc25c9201731c203dc9e18738560_1))))
                                                                                                     ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(145,10-145,34)
                                                                                                     (forall
                                                                                                       ((@x26
                                                                                                         Term))
                                                                                                      (! (implies
                                                                                                        (HasType
                                                                                                         @x26
                                                                                                         Prims.unit)
                                                                                                        ;; def=Prims.fst(467,77-467,89); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                                        (and
                                                                                                         ;; def=Pulse.Spec.GC.Graph.fst(85,61-85,77); use=Pulse.Spec.GC.GraphBridge.fst(149,38-149,42)
                                                                                                         (or
                                                                                                          label_21
                                                                                                          ;; def=Pulse.Spec.GC.Graph.fst(85,61-85,77); use=Pulse.Spec.GC.GraphBridge.fst(149,38-149,42)
                                                                                                          (BoxBool_proj_0
                                                                                                           (Pulse.Spec.GC.Graph.is_vertex_set
                                                                                                            (Pulse.Spec.GC.Fields.objects
                                                                                                             (FStar.UInt64.uint_to_t
                                                                                                              (Prims.op_Addition
                                                                                                               (FStar.UInt64.v
                                                                                                                x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                               (Prims.op_Multiply
                                                                                                                (Prims.op_Addition
                                                                                                                 (FStar.UInt64.v
                                                                                                                  (Pulse.Spec.GC.Object.getWosize
                                                                                                                   (Pulse.Spec.GC.Heap.read_word
                                                                                                                    x_e246fc25c9201731c203dc9e18738560_1
                                                                                                                    x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                                 (BoxInt
                                                                                                                  1))
                                                                                                                (BoxInt
                                                                                                                 8))))
                                                                                                             x_e246fc25c9201731c203dc9e18738560_1))))
                                                                                                         ;; def=Prims.fst(459,66-459,102); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                                         (forall
                                                                                                           ((@x27
                                                                                                             Term))
                                                                                                          (! (implies
                                                                                                            (and
                                                                                                             (HasType
                                                                                                              @x27
                                                                                                              (FStar.Seq.Base.seq
                                                                                                               U_zero
                                                                                                               Pulse.Spec.GC.Base.hp_addr))
                                                                                                             ;; def=Pulse.Spec.GC.Graph.fst(85,45-85,47); use=Pulse.Spec.GC.GraphBridge.fst(114,4-152,7)
                                                                                                             (=
                                                                                                              (Pulse.Spec.GC.Fields.objects
                                                                                                               (FStar.UInt64.uint_to_t
                                                                                                                (Prims.op_Addition
                                                                                                                 (FStar.UInt64.v
                                                                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                                 (Prims.op_Multiply
                                                                                                                  (Prims.op_Addition
                                                                                                                   (FStar.UInt64.v
                                                                                                                    (Pulse.Spec.GC.Object.getWosize
                                                                                                                     (Pulse.Spec.GC.Heap.read_word
                                                                                                                      x_e246fc25c9201731c203dc9e18738560_1
                                                                                                                      x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                                   (BoxInt
                                                                                                                    1))
                                                                                                                  (BoxInt
                                                                                                                   8))))
                                                                                                               x_e246fc25c9201731c203dc9e18738560_1)
                                                                                                              @x27))
                                                                                                            ;; def=Prims.fst(449,29-449,97); use=Pulse.Spec.GC.GraphBridge.fst(149,10-149,28)
                                                                                                            (and
                                                                                                             (or
                                                                                                              label_22
                                                                                                              (not
                                                                                                               (BoxBool_proj_0
                                                                                                                (FStar.Seq.Properties.mem
                                                                                                                 Pulse.Spec.GC.Graph.vertex_id
                                                                                                                 (Pulse.Spec.GC.Fields.obj_address
                                                                                                                  x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                                 (Pulse.Spec.GC.Fields.objects
                                                                                                                  (FStar.UInt64.uint_to_t
                                                                                                                   (Prims.op_Addition
                                                                                                                    (FStar.UInt64.v
                                                                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                                    (Prims.op_Multiply
                                                                                                                     (Prims.op_Addition
                                                                                                                      (FStar.UInt64.v
                                                                                                                       (Pulse.Spec.GC.Object.getWosize
                                                                                                                        (Pulse.Spec.GC.Heap.read_word
                                                                                                                         x_e246fc25c9201731c203dc9e18738560_1
                                                                                                                         x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                                      (BoxInt
                                                                                                                       1))
                                                                                                                     (BoxInt
                                                                                                                      8))))
                                                                                                                  x_e246fc25c9201731c203dc9e18738560_1)))))
                                                                                                             ;; def=Prims.fst(449,36-449,97); use=Pulse.Spec.GC.GraphBridge.fst(149,10-149,28)
                                                                                                             (forall
                                                                                                               ((@x28
                                                                                                                 Term))
                                                                                                              (! (implies
                                                                                                                (and
                                                                                                                 (HasType
                                                                                                                  @x28
                                                                                                                  Prims.unit)
                                                                                                                 ;; def=Pulse.Spec.GC.Graph.fst(87,17-87,47); use=Pulse.Spec.GC.GraphBridge.fst(149,10-149,28)
                                                                                                                 (BoxBool_proj_0
                                                                                                                  (Pulse.Spec.GC.Graph.is_vertex_set
                                                                                                                   (FStar.Seq.Base.cons
                                                                                                                    U_zero
                                                                                                                    Pulse.Spec.GC.Graph.vertex_id
                                                                                                                    (Pulse.Spec.GC.Fields.obj_address
                                                                                                                     x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                                    (Pulse.Spec.GC.Fields.objects
                                                                                                                     (FStar.UInt64.uint_to_t
                                                                                                                      (Prims.op_Addition
                                                                                                                       (FStar.UInt64.v
                                                                                                                        x_c39bed69b0e6a97dd42e9a16413dbcb1_0)
                                                                                                                       (Prims.op_Multiply
                                                                                                                        (Prims.op_Addition
                                                                                                                         (FStar.UInt64.v
                                                                                                                          (Pulse.Spec.GC.Object.getWosize
                                                                                                                           (Pulse.Spec.GC.Heap.read_word
                                                                                                                            x_e246fc25c9201731c203dc9e18738560_1
                                                                                                                            x_c39bed69b0e6a97dd42e9a16413dbcb1_0)))
                                                                                                                         (BoxInt
                                                                                                                          1))
                                                                                                                        (BoxInt
                                                                                                                         8))))
                                                                                                                     x_e246fc25c9201731c203dc9e18738560_1)))))
                                                                                                                ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(149,10-149,28)
                                                                                                                (Valid
                                                                                                                 ;; def=Prims.fst(449,83-449,96); use=Pulse.Spec.GC.GraphBridge.fst(149,10-149,28)
                                                                                                                 (ApplyTT
                                                                                                                  @x16
                                                                                                                  @x28)))
                                                                                                               :qid
                                                                                                                @query.35))))
                                                                                                           :qid
                                                                                                            @query.34))))
                                                                                                       :qid
                                                                                                        @query.33))))
                                                                                                   :qid
                                                                                                    @query.32)))
                                                                                                :qid
                                                                                                 @query.31)))
                                                                                             :qid
                                                                                              @query.30))))
                                                                                         :qid
                                                                                          @query.29))))
                                                                                     :qid @query.28)))
                                                                                  :qid @query.27))))
                                                                              :qid @query.26))))
                                                                          :qid @query.25))))
                                                                      :qid @query.24)))))
                                                                 :qid @query.21)))
                                                              :qid @query.20))))
                                                          :qid @query.19))))
                                                      :qid @query.18))))
                                                  :qid @query.17))))
                                              :qid @query.16))))
                                          :qid @query.15))))
                                      :qid @query.14))))
                                  :qid @query.13)))
                               :qid @query.12)))
                            :qid @query.11)))
                         :qid @query.10))))
                     :qid @query.9)))))
                :qid @query.6)))
             :qid @query.5)))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 100000000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_22")
(eval label_22)
(echo "label_21")
(eval label_21)
(echo "label_20")
(eval label_20)
(echo "label_19")
(eval label_19)
(echo "label_18")
(eval label_18)
(echo "label_17")
(eval label_17)
(echo "label_16")
(eval label_16)
(echo "label_15")
(eval label_15)
(echo "label_14")
(eval label_14)
(echo "label_13")
(eval label_13)
(echo "label_12")
(eval label_12)
(echo "label_11")
(eval label_11)
(echo "label_10")
(eval label_10)
(echo "label_9")
(eval label_9)
(echo "label_8")
(eval label_8)
(echo "label_7")
(eval label_7)
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Pulse.Spec.GC.GraphBridge.objects_no_duplicates, 1)
; STATUS: unknown because (incomplete quantifiers)
