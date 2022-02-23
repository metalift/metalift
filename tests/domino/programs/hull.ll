; ModuleID = 'tests/domino/programs/hull.ll'
source_filename = "tests/domino/programs/hull.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%struct.list = type { %"class.std::__1::vector" }
%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }
%"struct.std::__1::__default_init_tag" = type { i8 }
%"class.std::__1::__vector_base_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.0" = type { i8 }
%"class.std::__1::allocator" = type { i8 }
%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction" = type { %"class.std::__1::vector"*, i32*, i32* }
%"struct.std::__1::__split_buffer" = type { i32*, i32*, i32*, %"class.std::__1::__compressed_pair.1" }
%"class.std::__1::__compressed_pair.1" = type { %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem.2" }
%"struct.std::__1::__compressed_pair_elem.2" = type { %"class.std::__1::allocator"* }
%"struct.std::__1::integral_constant" = type { i8 }
%"struct.std::__1::__has_construct" = type { i8 }
%"struct.std::__1::__less" = type { i8 }
%"struct.std::__1::__has_max_size" = type { i8 }
%"class.std::__1::__split_buffer_common" = type { i8 }
%"class.std::length_error" = type { %"class.std::logic_error" }
%"class.std::logic_error" = type { %"class.std::exception", %"class.std::__1::__libcpp_refstring" }
%"class.std::exception" = type { i32 (...)** }
%"class.std::__1::__libcpp_refstring" = type { i8* }
%"struct.std::__1::integral_constant.3" = type { i8 }
%"struct.std::__1::__has_destroy" = type { i8 }
%"struct.std::__1::__has_construct.4" = type { i8 }

@.str = private unnamed_addr constant [68 x i8] c"allocator<T>::allocate(size_t n) 'n' exceeds maximum supported size\00", align 1
@_ZTISt12length_error = external constant i8*
@_ZTVSt12length_error = external unnamed_addr constant { [5 x i8*] }, align 8

; Function Attrs: noinline optnone ssp uwtable
define %struct.list* @test(i32 %arg, i32 %arg1, i32 %arg2, i32 %arg3, i32 %arg4) #0 {
bb:
  %i = alloca i32, align 4
  %i5 = alloca i32, align 4
  %i6 = alloca i32, align 4
  %i7 = alloca i32, align 4
  %i8 = alloca i32, align 4
  %i9 = alloca %struct.list*, align 8
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i5, align 4
  store i32 %arg2, i32* %i6, align 4
  store i32 %arg3, i32* %i7, align 4
  store i32 %arg4, i32* %i8, align 4
  %i10 = load i32, i32* %i, align 4
  %i11 = icmp slt i32 %i10, 0
  br i1 %i11, label %bb12, label %bb13

bb12:                                             ; preds = %bb
  store i32 0, i32* %i, align 4
  br label %bb15

bb13:                                             ; preds = %bb
  %i14 = load i32, i32* %i, align 4
  store i32 %i14, i32* %i, align 4
  br label %bb15

bb15:                                             ; preds = %bb13, %bb12
  %i16 = load i32, i32* %i7, align 4
  %i17 = load i32, i32* %i, align 4
  %i18 = add nsw i32 %i17, %i16
  store i32 %i18, i32* %i, align 4
  %i19 = load i32, i32* %i6, align 4
  %i20 = icmp sgt i32 %i19, 20
  br i1 %i20, label %bb21, label %bb22

bb21:                                             ; preds = %bb15
  store i32 1, i32* %i6, align 4
  br label %bb24

bb22:                                             ; preds = %bb15
  %i23 = load i32, i32* %i6, align 4
  store i32 %i23, i32* %i6, align 4
  br label %bb24

bb24:                                             ; preds = %bb22, %bb21
  %i25 = load i32, i32* %i8, align 4
  store i32 %i25, i32* %i5, align 4
  %i26 = call %struct.list* @_Z7newListIiEP4listIT_Ev()
  store %struct.list* %i26, %struct.list** %i9, align 8
  %i27 = load %struct.list*, %struct.list** %i9, align 8
  %i28 = load i32, i32* %i, align 4
  %i29 = call %struct.list* @_Z10listAppendIiEP4listIT_ES3_S1_(%struct.list* %i27, i32 %i28)
  store %struct.list* %i29, %struct.list** %i9, align 8
  %i30 = load %struct.list*, %struct.list** %i9, align 8
  %i31 = load i32, i32* %i5, align 4
  %i32 = call %struct.list* @_Z10listAppendIiEP4listIT_ES3_S1_(%struct.list* %i30, i32 %i31)
  store %struct.list* %i32, %struct.list** %i9, align 8
  %i33 = load %struct.list*, %struct.list** %i9, align 8
  %i34 = load i32, i32* %i6, align 4
  %i35 = call %struct.list* @_Z10listAppendIiEP4listIT_ES3_S1_(%struct.list* %i33, i32 %i34)
  store %struct.list* %i35, %struct.list** %i9, align 8
  %i36 = load %struct.list*, %struct.list** %i9, align 8
  ret %struct.list* %i36
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr %struct.list* @_Z7newListIiEP4listIT_Ev() #0 {
bb:
  %i = call noalias nonnull i8* @_Znwm(i64 24) #11
  %i1 = bitcast i8* %i to %struct.list*
  %i2 = bitcast %struct.list* %i1 to i8*
  call void @llvm.memset.p0i8.i64(i8* align 16 %i2, i8 0, i64 24, i1 false)
  call void @_ZN4listIiEC1Ev(%struct.list* %i1) #12
  ret %struct.list* %i1
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr %struct.list* @_Z10listAppendIiEP4listIT_ES3_S1_(%struct.list* %arg, i32 %arg1) #0 {
bb:
  %i = alloca %struct.list*, align 8
  %i2 = alloca i32, align 4
  %i3 = alloca %struct.list*, align 8
  %i4 = alloca i32, align 4
  %i5 = alloca i32, align 4
  store %struct.list* %arg, %struct.list** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i6 = call %struct.list* @_Z7newListIiEP4listIT_Ev()
  store %struct.list* %i6, %struct.list** %i3, align 8
  store i32 0, i32* %i4, align 4
  br label %bb7

bb7:                                              ; preds = %bb18, %bb
  %i8 = load i32, i32* %i4, align 4
  %i9 = load %struct.list*, %struct.list** %i, align 8
  %i10 = call i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %i9)
  %i11 = icmp slt i32 %i8, %i10
  br i1 %i11, label %bb12, label %bb21

bb12:                                             ; preds = %bb7
  %i13 = load %struct.list*, %struct.list** %i3, align 8
  %i14 = getelementptr inbounds %struct.list, %struct.list* %i13, i32 0, i32 0
  %i15 = load %struct.list*, %struct.list** %i, align 8
  %i16 = load i32, i32* %i4, align 4
  %i17 = call i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %i15, i32 %i16)
  store i32 %i17, i32* %i5, align 4
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backEOi(%"class.std::__1::vector"* %i14, i32* nonnull align 4 dereferenceable(4) %i5)
  br label %bb18

bb18:                                             ; preds = %bb12
  %i19 = load i32, i32* %i4, align 4
  %i20 = add nsw i32 %i19, 1
  store i32 %i20, i32* %i4, align 4
  br label %bb7

bb21:                                             ; preds = %bb7
  %i22 = load %struct.list*, %struct.list** %i3, align 8
  %i23 = getelementptr inbounds %struct.list, %struct.list* %i22, i32 0, i32 0
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector"* %i23, i32* nonnull align 4 dereferenceable(4) %i2)
  %i24 = load %struct.list*, %struct.list** %i3, align 8
  ret %struct.list* %i24
}

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #1

; Function Attrs: argmemonly nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #2

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZN4listIiEC1Ev(%struct.list* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %struct.list*, align 8
  store %struct.list* %arg, %struct.list** %i, align 8
  %i1 = load %struct.list*, %struct.list** %i, align 8
  call void @_ZN4listIiEC2Ev(%struct.list* %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZN4listIiEC2Ev(%struct.list* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %struct.list*, align 8
  store %struct.list* %arg, %struct.list** %i, align 8
  %i1 = load %struct.list*, %struct.list** %i, align 8
  %i2 = getelementptr inbounds %struct.list, %struct.list* %i1, i32 0, i32 0
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %i2) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %i2) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %arg) unnamed_addr #3 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  %i1 = alloca i8*, align 8
  %i2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i3 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i4 = bitcast %"class.std::__1::__vector_base"* %i3 to %"class.std::__1::__vector_base_common"*
  call void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i4)
  br label %bb5

bb5:                                              ; preds = %bb
  %i6 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 0
  store i32* null, i32** %i6, align 8
  %i7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 1
  store i32* null, i32** %i7, align 8
  %i8 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 2
  store i8* null, i8** %i1, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %i8, i8** nonnull align 8 dereferenceable(8) %i1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i2)
  br label %bb9

bb9:                                              ; preds = %bb5
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base_common"*, align 8
  store %"class.std::__1::__vector_base_common"* %arg, %"class.std::__1::__vector_base_common"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base_common"*, %"class.std::__1::__vector_base_common"** %i, align 8
  ret void
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: noinline noreturn nounwind
define linkonce_odr hidden void @__clang_call_terminate(i8* %arg) #4 {
bb:
  %i = call i8* @__cxa_begin_catch(i8* %arg) #12
  call void @_ZSt9terminatev() #13
  unreachable
}

declare i8* @__cxa_begin_catch(i8*)

declare void @_ZSt9terminatev()

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %arg, i8** nonnull align 8 dereferenceable(8) %arg1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  %i3 = alloca i8**, align 8
  %i4 = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  store i8** %arg1, i8*** %i3, align 8
  store %"struct.std::__1::__default_init_tag"* %arg2, %"struct.std::__1::__default_init_tag"** %i4, align 8
  %i5 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i6 = load i8**, i8*** %i3, align 8
  %i7 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %i4, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %i5, i8** nonnull align 8 dereferenceable(8) %i6, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %arg, i8** nonnull align 8 dereferenceable(8) %arg1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  %i3 = alloca i8**, align 8
  %i4 = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %i5 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  store i8** %arg1, i8*** %i3, align 8
  store %"struct.std::__1::__default_init_tag"* %arg2, %"struct.std::__1::__default_init_tag"** %i4, align 8
  %i6 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i7 = bitcast %"class.std::__1::__compressed_pair"* %i6 to %"struct.std::__1::__compressed_pair_elem"*
  %i8 = load i8**, i8*** %i3, align 8
  %i9 = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i8) #12
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i7, i8** nonnull align 8 dereferenceable(8) %i9)
  %i10 = bitcast %"class.std::__1::__compressed_pair"* %i6 to %"struct.std::__1::__compressed_pair_elem.0"*
  %i11 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %i4, align 8
  %i12 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i11) #12
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %i10)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %arg) #3 {
bb:
  %i = alloca i8**, align 8
  store i8** %arg, i8*** %i, align 8
  %i1 = load i8**, i8*** %i, align 8
  ret i8** %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %arg, i8** nonnull align 8 dereferenceable(8) %arg1) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  %i2 = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  store i8** %arg1, i8*** %i2, align 8
  %i3 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  %i4 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %i3, i32 0, i32 0
  %i5 = load i8**, i8*** %i2, align 8
  %i6 = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i5) #12
  store i32* null, i32** %i4, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %arg) #3 {
bb:
  %i = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"struct.std::__1::__default_init_tag"* %arg, %"struct.std::__1::__default_init_tag"** %i, align 8
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %i, align 8
  ret %"struct.std::__1::__default_init_tag"* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %i1 = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %i1, align 8
  %i2 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %i1, align 8
  %i3 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %i2 to %"class.std::__1::allocator"*
  call void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %i3) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %arg) #3 {
bb:
  %i = alloca %struct.list*, align 8
  store %struct.list* %arg, %struct.list** %i, align 8
  %i1 = load %struct.list*, %struct.list** %i, align 8
  %i2 = getelementptr inbounds %struct.list, %struct.list* %i1, i32 0, i32 0
  %i3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i2) #12
  %i4 = trunc i64 %i3 to i32
  ret i32 %i4
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backEOi(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i4 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i4, i32 0, i32 1
  %i6 = load i32*, i32** %i5, align 8
  %i7 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i8 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i7) #12
  %i9 = load i32*, i32** %i8, align 8
  %i10 = icmp ult i32* %i6, %i9
  br i1 %i10, label %bb11, label %bb14

bb11:                                             ; preds = %bb
  %i12 = load i32*, i32** %i2, align 8
  %i13 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %i12) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJiEEEvDpOT_(%"class.std::__1::vector"* %i3, i32* nonnull align 4 dereferenceable(4) %i13)
  br label %bb17

bb14:                                             ; preds = %bb
  %i15 = load i32*, i32** %i2, align 8
  %i16 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %i15) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIiEEvOT_(%"class.std::__1::vector"* %i3, i32* nonnull align 4 dereferenceable(4) %i16)
  br label %bb17

bb17:                                             ; preds = %bb14, %bb11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %arg, i32 %arg1) #3 {
bb:
  %i = alloca %struct.list*, align 8
  %i2 = alloca i32, align 4
  store %struct.list* %arg, %struct.list** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i3 = load %struct.list*, %struct.list** %i, align 8
  %i4 = getelementptr inbounds %struct.list, %struct.list* %i3, i32 0, i32 0
  %i5 = load i32, i32* %i2, align 4
  %i6 = sext i32 %i5 to i64
  %i7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %i4, i64 %i6) #12
  %i8 = load i32, i32* %i7, align 4
  ret i32 %i8
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i4 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i4, i32 0, i32 1
  %i6 = load i32*, i32** %i5, align 8
  %i7 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i8 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i7) #12
  %i9 = load i32*, i32** %i8, align 8
  %i10 = icmp ne i32* %i6, %i9
  br i1 %i10, label %bb11, label %bb13

bb11:                                             ; preds = %bb
  %i12 = load i32*, i32** %i2, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector"* %i3, i32* nonnull align 4 dereferenceable(4) %i12)
  br label %bb15

bb13:                                             ; preds = %bb
  %i14 = load i32*, i32** %i2, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector"* %i3, i32* nonnull align 4 dereferenceable(4) %i14)
  br label %bb15

bb15:                                             ; preds = %bb13, %bb11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %i3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  %i4 = load i32*, i32** %i3, align 8
  %i5 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %i6 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i5, i32 0, i32 0
  %i7 = load i32*, i32** %i6, align 8
  %i8 = ptrtoint i32* %i4 to i64
  %i9 = ptrtoint i32* %i7 to i64
  %i10 = sub i64 %i8, %i9
  %i11 = sdiv exact i64 %i10, 4
  ret i64 %i11
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 2
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJiEEEvDpOT_(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", align 8
  %i4 = alloca i8*, align 8
  %i5 = alloca i32, align 4
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i6 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i6, i64 1)
  %i7 = bitcast %"class.std::__1::vector"* %i6 to %"class.std::__1::__vector_base"*
  %i8 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i7) #12
  %i9 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, i32 0, i32 1
  %i10 = load i32*, i32** %i9, align 8
  %i11 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i10) #12
  %i12 = load i32*, i32** %i2, align 8
  %i13 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i12) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i8, i32* %i11, i32* nonnull align 4 dereferenceable(4) %i13)
  br label %bb14

bb14:                                             ; preds = %bb
  %i15 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, i32 0, i32 1
  %i16 = load i32*, i32** %i15, align 8
  %i17 = getelementptr inbounds i32, i32* %i16, i32 1
  store i32* %i17, i32** %i15, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %arg) #3 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIiEEvOT_(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"class.std::__1::allocator"*, align 8
  %i4 = alloca %"struct.std::__1::__split_buffer", align 8
  %i5 = alloca i8*, align 8
  %i6 = alloca i32, align 4
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i8 = bitcast %"class.std::__1::vector"* %i7 to %"class.std::__1::__vector_base"*
  %i9 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i8) #12
  store %"class.std::__1::allocator"* %i9, %"class.std::__1::allocator"** %i3, align 8
  %i10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i7) #12
  %i11 = add i64 %i10, 1
  %i12 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %i7, i64 %i11)
  %i13 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i7) #12
  %i14 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %i4, i64 %i12, i64 %i13, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i14)
  %i15 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  %i16 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i17 = load i32*, i32** %i16, align 8
  %i18 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i17) #12
  %i19 = load i32*, i32** %i2, align 8
  %i20 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i19) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i15, i32* %i18, i32* nonnull align 4 dereferenceable(4) %i20)
  br label %bb21

bb21:                                             ; preds = %bb
  %i22 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i23 = load i32*, i32** %i22, align 8
  %i24 = getelementptr inbounds i32, i32* %i23, i32 1
  store i32* %i24, i32** %i22, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %i7, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %i4)
  br label %bb25

bb25:                                             ; preds = %bb21
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %i4) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %i1 to %"struct.std::__1::__compressed_pair_elem"*
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  %i1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %i1, i32 0, i32 0
  ret i32** %i2
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %arg1, i64 %arg2) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %i3 = alloca %"class.std::__1::vector"*, align 8
  %i4 = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  store %"class.std::__1::vector"* %arg1, %"class.std::__1::vector"** %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  %i6 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i3, align 8
  %i7 = load i64, i64* %i4, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i5, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i6, i64 %i7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca %"struct.std::__1::integral_constant", align 1
  %i6 = alloca %"struct.std::__1::__has_construct", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i7 = bitcast %"struct.std::__1::__has_construct"* %i6 to %"struct.std::__1::integral_constant"*
  %i8 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i9 = load i32*, i32** %i3, align 8
  %i10 = load i32*, i32** %i4, align 8
  %i11 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i10) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i8, i32* %i9, i32* nonnull align 4 dereferenceable(4) %i11)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 2
  %i3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %i2) #12
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %arg) #3 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %arg) #3 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  %i1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %arg1, i64 %arg2) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %i3 = alloca %"class.std::__1::vector"*, align 8
  %i4 = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  store %"class.std::__1::vector"* %arg1, %"class.std::__1::vector"** %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  %i6 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i5, i32 0, i32 0
  %i7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i3, align 8
  store %"class.std::__1::vector"* %i7, %"class.std::__1::vector"** %i6, align 8
  %i8 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i5, i32 0, i32 1
  %i9 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i3, align 8
  %i10 = bitcast %"class.std::__1::vector"* %i9 to %"class.std::__1::__vector_base"*
  %i11 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i10, i32 0, i32 1
  %i12 = load i32*, i32** %i11, align 8
  store i32* %i12, i32** %i8, align 8
  %i13 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i5, i32 0, i32 2
  %i14 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i3, align 8
  %i15 = bitcast %"class.std::__1::vector"* %i14 to %"class.std::__1::__vector_base"*
  %i16 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i15, i32 0, i32 1
  %i17 = load i32*, i32** %i16, align 8
  %i18 = load i64, i64* %i4, align 8
  %i19 = getelementptr inbounds i32, i32* %i17, i64 %i18
  store i32* %i19, i32** %i13, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %i3 = alloca %"class.std::__1::allocator"*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i3, align 8
  store i32* %arg1, i32** %i4, align 8
  store i32* %arg2, i32** %i5, align 8
  %i6 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  %i7 = load i32*, i32** %i4, align 8
  %i8 = load i32*, i32** %i5, align 8
  %i9 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i8) #12
  call void @_ZNSt3__19allocatorIiE9constructIiJiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %i6, i32* %i7, i32* nonnull align 4 dereferenceable(4) %i9)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorIiE9constructIiJiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i6 = load i32*, i32** %i3, align 8
  %i7 = bitcast i32* %i6 to i8*
  %i8 = bitcast i8* %i7 to i32*
  %i9 = load i32*, i32** %i4, align 8
  %i10 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i9) #12
  %i11 = load i32, i32* %i10, align 4
  store i32 %i11, i32* %i8, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %i1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %i3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i2) #12
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %i, align 8
  %i1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %i, align 8
  %i2 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %i1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  %i1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i1, i32 0, i32 1
  %i3 = load i32*, i32** %i2, align 8
  %i4 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i1, i32 0, i32 0
  %i5 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i4, align 8
  %i6 = bitcast %"class.std::__1::vector"* %i5 to %"class.std::__1::__vector_base"*
  %i7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i6, i32 0, i32 1
  store i32* %i3, i32** %i7, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %arg, i64 %arg1) #0 align 2 {
bb:
  %i = alloca i64, align 8
  %i2 = alloca %"class.std::__1::vector"*, align 8
  %i3 = alloca i64, align 8
  %i4 = alloca i64, align 8
  %i5 = alloca i64, align 8
  %i6 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i2, align 8
  store i64 %arg1, i64* %i3, align 8
  %i7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i2, align 8
  %i8 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %i7) #12
  store i64 %i8, i64* %i4, align 8
  %i9 = load i64, i64* %i3, align 8
  %i10 = load i64, i64* %i4, align 8
  %i11 = icmp ugt i64 %i9, %i10
  br i1 %i11, label %bb12, label %bb14

bb12:                                             ; preds = %bb
  %i13 = bitcast %"class.std::__1::vector"* %i7 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i13) #14
  unreachable

bb14:                                             ; preds = %bb
  %i15 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %i7) #12
  store i64 %i15, i64* %i5, align 8
  %i16 = load i64, i64* %i5, align 8
  %i17 = load i64, i64* %i4, align 8
  %i18 = udiv i64 %i17, 2
  %i19 = icmp uge i64 %i16, %i18
  br i1 %i19, label %bb20, label %bb22

bb20:                                             ; preds = %bb14
  %i21 = load i64, i64* %i4, align 8
  store i64 %i21, i64* %i, align 8
  br label %bb27

bb22:                                             ; preds = %bb14
  %i23 = load i64, i64* %i5, align 8
  %i24 = mul i64 2, %i23
  store i64 %i24, i64* %i6, align 8
  %i25 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %i6, i64* nonnull align 8 dereferenceable(8) %i3)
  %i26 = load i64, i64* %i25, align 8
  store i64 %i26, i64* %i, align 8
  br label %bb27

bb27:                                             ; preds = %bb22, %bb20
  %i28 = load i64, i64* %i, align 8
  ret i64 %i28
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %arg, i64 %arg1, i64 %arg2, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg3) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  %i4 = alloca i64, align 8
  %i5 = alloca i64, align 8
  %i6 = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  store i64 %arg1, i64* %i4, align 8
  store i64 %arg2, i64* %i5, align 8
  store %"class.std::__1::allocator"* %arg3, %"class.std::__1::allocator"** %i6, align 8
  %i7 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i8 = load i64, i64* %i4, align 8
  %i9 = load i64, i64* %i5, align 8
  %i10 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i6, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %i7, i64 %i8, i64 %i9, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i10)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %arg, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store %"struct.std::__1::__split_buffer"* %arg1, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %i3) #12
  %i4 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i5 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i4) #12
  %i6 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i6, i32 0, i32 0
  %i8 = load i32*, i32** %i7, align 8
  %i9 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i10 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i9, i32 0, i32 1
  %i11 = load i32*, i32** %i10, align 8
  %i12 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i13 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i12, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5, i32* %i8, i32* %i11, i32** nonnull align 8 dereferenceable(8) %i13)
  %i14 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i15 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i14, i32 0, i32 0
  %i16 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i17 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i16, i32 0, i32 1
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %i15, i32** nonnull align 8 dereferenceable(8) %i17) #12
  %i18 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i19 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i18, i32 0, i32 1
  %i20 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i21 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i20, i32 0, i32 2
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %i19, i32** nonnull align 8 dereferenceable(8) %i21) #12
  %i22 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i23 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i22) #12
  %i24 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i25 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i24) #12
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %i23, i32** nonnull align 8 dereferenceable(8) %i25) #12
  %i26 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i27 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i26, i32 0, i32 1
  %i28 = load i32*, i32** %i27, align 8
  %i29 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  %i30 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i29, i32 0, i32 0
  store i32* %i28, i32** %i30, align 8
  %i31 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i3) #12
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %i3, i64 %i31) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %i3)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %arg) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %arg) #3 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i1 = alloca i64, align 8
  %i2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i4 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i5 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i4) #12
  %i6 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5) #12
  store i64 %i6, i64* %i1, align 8
  %i7 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #12
  store i64 %i7, i64* %i2, align 8
  %i8 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %i1, i64* nonnull align 8 dereferenceable(8) %i2)
  br label %bb9

bb9:                                              ; preds = %bb
  %i10 = load i64, i64* %i8, align 8
  ret i64 %i10
}

; Function Attrs: noreturn
declare void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"*) #5

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %i3 = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %i2) #12
  ret i64 %i3
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %arg, i64* nonnull align 8 dereferenceable(8) %arg1) #0 {
bb:
  %i = alloca i64*, align 8
  %i2 = alloca i64*, align 8
  %i3 = alloca %"struct.std::__1::__less", align 1
  store i64* %arg, i64** %i, align 8
  store i64* %arg1, i64** %i2, align 8
  %i4 = load i64*, i64** %i, align 8
  %i5 = load i64*, i64** %i2, align 8
  %i6 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %i4, i64* nonnull align 8 dereferenceable(8) %i5)
  ret i64* %i6
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %arg, i64* nonnull align 8 dereferenceable(8) %arg1) #0 {
bb:
  %i = alloca i64*, align 8
  %i2 = alloca i64*, align 8
  %i3 = alloca %"struct.std::__1::__less", align 1
  store i64* %arg, i64** %i, align 8
  store i64* %arg1, i64** %i2, align 8
  %i4 = load i64*, i64** %i, align 8
  %i5 = load i64*, i64** %i2, align 8
  %i6 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %i4, i64* nonnull align 8 dereferenceable(8) %i5)
  ret i64* %i6
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i1 = alloca %"struct.std::__1::integral_constant", align 1
  %i2 = alloca %"struct.std::__1::__has_max_size", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  %i3 = bitcast %"struct.std::__1::__has_max_size"* %i2 to %"struct.std::__1::integral_constant"*
  %i4 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i5 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i4) #12
  ret i64 %i5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 2
  %i3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %i2) #12
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #3 align 2 {
bb:
  %i = call i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #12
  ret i64 %i
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %arg, i64* nonnull align 8 dereferenceable(8) %arg1) #0 {
bb:
  %i = alloca %"struct.std::__1::__less", align 1
  %i2 = alloca i64*, align 8
  %i3 = alloca i64*, align 8
  store i64* %arg, i64** %i2, align 8
  store i64* %arg1, i64** %i3, align 8
  %i4 = load i64*, i64** %i3, align 8
  %i5 = load i64*, i64** %i2, align 8
  %i6 = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %i, i64* nonnull align 8 dereferenceable(8) %i4, i64* nonnull align 8 dereferenceable(8) %i5)
  br i1 %i6, label %bb7, label %bb9

bb7:                                              ; preds = %bb
  %i8 = load i64*, i64** %i3, align 8
  br label %bb11

bb9:                                              ; preds = %bb
  %i10 = load i64*, i64** %i2, align 8
  br label %bb11

bb11:                                             ; preds = %bb9, %bb7
  %i12 = phi i64* [ %i8, %bb7 ], [ %i10, %bb9 ]
  ret i64* %i12
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %arg, i64* nonnull align 8 dereferenceable(8) %arg1, i64* nonnull align 8 dereferenceable(8) %arg2) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__less"*, align 8
  %i3 = alloca i64*, align 8
  %i4 = alloca i64*, align 8
  store %"struct.std::__1::__less"* %arg, %"struct.std::__1::__less"** %i, align 8
  store i64* %arg1, i64** %i3, align 8
  store i64* %arg2, i64** %i4, align 8
  %i5 = load %"struct.std::__1::__less"*, %"struct.std::__1::__less"** %i, align 8
  %i6 = load i64*, i64** %i3, align 8
  %i7 = load i64, i64* %i6, align 8
  %i8 = load i64*, i64** %i4, align 8
  %i9 = load i64, i64* %i8, align 8
  %i10 = icmp ult i64 %i7, %i9
  ret i1 %i10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %i1 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i1, align 8
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i1, align 8
  %i3 = call i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %i2) #12
  ret i64 %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  ret i64 4611686018427387903
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %i1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %i3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i2) #12
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %i, align 8
  %i1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %i, align 8
  %i2 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %i1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #3 align 2 {
bb:
  ret i64 9223372036854775807
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i2 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i1) #12
  %i3 = load i32*, i32** %i2, align 8
  %i4 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 0
  %i5 = load i32*, i32** %i4, align 8
  %i6 = ptrtoint i32* %i3 to i64
  %i7 = ptrtoint i32* %i5 to i64
  %i8 = sub i64 %i6, %i7
  %i9 = sdiv exact i64 %i8, 4
  ret i64 %i9
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %i, align 8
  %i1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 2
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %i1 to %"struct.std::__1::__compressed_pair_elem"*
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  %i1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %i1, i32 0, i32 0
  ret i32** %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %arg, i64* nonnull align 8 dereferenceable(8) %arg1) #3 {
bb:
  %i = alloca %"struct.std::__1::__less", align 1
  %i2 = alloca i64*, align 8
  %i3 = alloca i64*, align 8
  store i64* %arg, i64** %i2, align 8
  store i64* %arg1, i64** %i3, align 8
  %i4 = load i64*, i64** %i2, align 8
  %i5 = load i64*, i64** %i3, align 8
  %i6 = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %i, i64* nonnull align 8 dereferenceable(8) %i4, i64* nonnull align 8 dereferenceable(8) %i5)
  br i1 %i6, label %bb7, label %bb9

bb7:                                              ; preds = %bb
  %i8 = load i64*, i64** %i3, align 8
  br label %bb11

bb9:                                              ; preds = %bb
  %i10 = load i64*, i64** %i2, align 8
  br label %bb11

bb11:                                             ; preds = %bb9, %bb7
  %i12 = phi i64* [ %i8, %bb7 ], [ %i10, %bb9 ]
  ret i64* %i12
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %arg, i64 %arg1, i64 %arg2, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg3) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  %i4 = alloca i64, align 8
  %i5 = alloca i64, align 8
  %i6 = alloca %"class.std::__1::allocator"*, align 8
  %i7 = alloca i8*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  store i64 %arg1, i64* %i4, align 8
  store i64 %arg2, i64* %i5, align 8
  store %"class.std::__1::allocator"* %arg3, %"class.std::__1::allocator"** %i6, align 8
  %i8 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i9 = bitcast %"struct.std::__1::__split_buffer"* %i8 to %"class.std::__1::__split_buffer_common"*
  %i10 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 3
  store i8* null, i8** %i7, align 8
  %i11 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i6, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %i10, i8** nonnull align 8 dereferenceable(8) %i7, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i11)
  %i12 = load i64, i64* %i4, align 8
  %i13 = icmp ne i64 %i12, 0
  br i1 %i13, label %bb14, label %bb18

bb14:                                             ; preds = %bb
  %i15 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %i8) #12
  %i16 = load i64, i64* %i4, align 8
  %i17 = call i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i15, i64 %i16)
  br label %bb19

bb18:                                             ; preds = %bb
  br label %bb19

bb19:                                             ; preds = %bb18, %bb14
  %i20 = phi i32* [ %i17, %bb14 ], [ null, %bb18 ]
  %i21 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 0
  store i32* %i20, i32** %i21, align 8
  %i22 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 0
  %i23 = load i32*, i32** %i22, align 8
  %i24 = load i64, i64* %i5, align 8
  %i25 = getelementptr inbounds i32, i32* %i23, i64 %i24
  %i26 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 2
  store i32* %i25, i32** %i26, align 8
  %i27 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 1
  store i32* %i25, i32** %i27, align 8
  %i28 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i8, i32 0, i32 0
  %i29 = load i32*, i32** %i28, align 8
  %i30 = load i64, i64* %i4, align 8
  %i31 = getelementptr inbounds i32, i32* %i29, i64 %i30
  %i32 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i8) #12
  store i32* %i31, i32** %i32, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %arg, i8** nonnull align 8 dereferenceable(8) %arg1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  %i3 = alloca i8**, align 8
  %i4 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %i, align 8
  store i8** %arg1, i8*** %i3, align 8
  store %"class.std::__1::allocator"* %arg2, %"class.std::__1::allocator"** %i4, align 8
  %i5 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i6 = load i8**, i8*** %i3, align 8
  %i7 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i4, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %i5, i8** nonnull align 8 dereferenceable(8) %i6, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i64 %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i2 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i4 = load i64, i64* %i2, align 8
  %i5 = call i32* @_ZNSt3__19allocatorIiE8allocateEm(%"class.std::__1::allocator"* %i3, i64 %i4)
  ret i32* %i5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 3
  %i3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.1"* %i2) #12
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 3
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %arg, i8** nonnull align 8 dereferenceable(8) %arg1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  %i3 = alloca i8**, align 8
  %i4 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %i, align 8
  store i8** %arg1, i8*** %i3, align 8
  store %"class.std::__1::allocator"* %arg2, %"class.std::__1::allocator"** %i4, align 8
  %i5 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i6 = bitcast %"class.std::__1::__compressed_pair.1"* %i5 to %"struct.std::__1::__compressed_pair_elem"*
  %i7 = load i8**, i8*** %i3, align 8
  %i8 = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i7) #12
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i6, i8** nonnull align 8 dereferenceable(8) %i8)
  %i9 = bitcast %"class.std::__1::__compressed_pair.1"* %i5 to i8*
  %i10 = getelementptr inbounds i8, i8* %i9, i64 8
  %i11 = bitcast i8* %i10 to %"struct.std::__1::__compressed_pair_elem.2"*
  %i12 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i4, align 8
  %i13 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i12) #12
  call void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %i11, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i13)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg) #3 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  ret %"class.std::__1::allocator"* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %arg, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg1) unnamed_addr #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  %i2 = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %arg, %"struct.std::__1::__compressed_pair_elem.2"** %i, align 8
  store %"class.std::__1::allocator"* %arg1, %"class.std::__1::allocator"** %i2, align 8
  %i3 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %i, align 8
  %i4 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.2", %"struct.std::__1::__compressed_pair_elem.2"* %i3, i32 0, i32 0
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i2, align 8
  %i6 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5) #12
  store %"class.std::__1::allocator"* %i6, %"class.std::__1::allocator"** %i4, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__19allocatorIiE8allocateEm(%"class.std::__1::allocator"* %arg, i64 %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i2 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i4 = load i64, i64* %i2, align 8
  %i5 = icmp ugt i64 %i4, 4611686018427387903
  br i1 %i5, label %bb6, label %bb7

bb6:                                              ; preds = %bb
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str, i64 0, i64 0)) #14
  unreachable

bb7:                                              ; preds = %bb
  %i8 = load i64, i64* %i2, align 8
  %i9 = mul i64 %i8, 4
  %i10 = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %i9, i64 4)
  %i11 = bitcast i8* %i10 to i32*
  ret i32* %i11
}

; Function Attrs: noinline noreturn optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__throw_length_errorEPKc(i8* %arg) #6 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca i8*, align 8
  %i1 = alloca i8*, align 8
  %i2 = alloca i32, align 4
  store i8* %arg, i8** %i, align 8
  %i3 = call i8* @__cxa_allocate_exception(i64 16) #12
  %i4 = bitcast i8* %i3 to %"class.std::length_error"*
  %i5 = load i8*, i8** %i, align 8
  call void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %i4, i8* %i5)
  br label %bb6

bb6:                                              ; preds = %bb
  call void @__cxa_throw(i8* %i3, i8* bitcast (i8** @_ZTISt12length_error to i8*), i8* bitcast (void (%"class.std::length_error"*)* @_ZNSt12length_errorD1Ev to i8*)) #14
  unreachable
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %arg, i64 %arg1) #0 {
bb:
  %i = alloca i64, align 8
  %i2 = alloca i64, align 8
  store i64 %arg, i64* %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load i64, i64* %i, align 8
  %i4 = call noalias nonnull i8* @_Znwm(i64 %i3) #11
  ret i8* %i4
}

declare i8* @__cxa_allocate_exception(i64)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %arg, i8* %arg1) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::length_error"*, align 8
  %i2 = alloca i8*, align 8
  store %"class.std::length_error"* %arg, %"class.std::length_error"** %i, align 8
  store i8* %arg1, i8** %i2, align 8
  %i3 = load %"class.std::length_error"*, %"class.std::length_error"** %i, align 8
  %i4 = load i8*, i8** %i2, align 8
  call void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %i3, i8* %i4)
  ret void
}

declare void @__cxa_free_exception(i8*)

; Function Attrs: nounwind
declare void @_ZNSt12length_errorD1Ev(%"class.std::length_error"*) unnamed_addr #7

declare void @__cxa_throw(i8*, i8*, i8*)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %arg, i8* %arg1) unnamed_addr #0 align 2 {
bb:
  %i = alloca %"class.std::length_error"*, align 8
  %i2 = alloca i8*, align 8
  store %"class.std::length_error"* %arg, %"class.std::length_error"** %i, align 8
  store i8* %arg1, i8** %i2, align 8
  %i3 = load %"class.std::length_error"*, %"class.std::length_error"** %i, align 8
  %i4 = bitcast %"class.std::length_error"* %i3 to %"class.std::logic_error"*
  %i5 = load i8*, i8** %i2, align 8
  call void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"* %i4, i8* %i5)
  %i6 = bitcast %"class.std::length_error"* %i3 to i32 (...)***
  store i32 (...)** bitcast (i8** getelementptr inbounds ({ [5 x i8*] }, { [5 x i8*] }* @_ZTVSt12length_error, i32 0, inrange i32 0, i32 2) to i32 (...)**), i32 (...)*** %i6, align 8
  ret void
}

declare void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"*, i8*) unnamed_addr #8

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.1"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair.1"* %i1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.2"*
  %i5 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %i4) #12
  ret %"class.std::__1::allocator"* %i5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %arg, %"struct.std::__1::__compressed_pair_elem.2"** %i, align 8
  %i1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.2", %"struct.std::__1::__compressed_pair_elem.2"* %i1, i32 0, i32 0
  %i3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i2, align 8
  ret %"class.std::__1::allocator"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair.1"* %i1 to %"struct.std::__1::__compressed_pair_elem"*
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i1) #12
  %i3 = bitcast i32* %i2 to i8*
  %i4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i1) #12
  %i5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %i1) #12
  %i6 = getelementptr inbounds i32, i32* %i4, i64 %i5
  %i7 = bitcast i32* %i6 to i8*
  %i8 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i1) #12
  %i9 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i1) #12
  %i10 = getelementptr inbounds i32, i32* %i8, i64 %i9
  %i11 = bitcast i32* %i10 to i8*
  %i12 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i1) #12
  %i13 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %i1) #12
  %i14 = getelementptr inbounds i32, i32* %i12, i64 %i13
  %i15 = bitcast i32* %i14 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %i1, i8* %i3, i8* %i7, i8* %i11, i8* %i15) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i32* %arg2, i32** nonnull align 8 dereferenceable(8) %arg3) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca i32*, align 8
  %i6 = alloca i32**, align 8
  %i7 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i4, align 8
  store i32* %arg2, i32** %i5, align 8
  store i32** %arg3, i32*** %i6, align 8
  %i8 = load i32*, i32** %i5, align 8
  %i9 = load i32*, i32** %i4, align 8
  %i10 = ptrtoint i32* %i8 to i64
  %i11 = ptrtoint i32* %i9 to i64
  %i12 = sub i64 %i10, %i11
  %i13 = sdiv exact i64 %i12, 4
  store i64 %i13, i64* %i7, align 8
  %i14 = load i64, i64* %i7, align 8
  %i15 = load i32**, i32*** %i6, align 8
  %i16 = load i32*, i32** %i15, align 8
  %i17 = sub i64 0, %i14
  %i18 = getelementptr inbounds i32, i32* %i16, i64 %i17
  store i32* %i18, i32** %i15, align 8
  %i19 = load i64, i64* %i7, align 8
  %i20 = icmp sgt i64 %i19, 0
  br i1 %i20, label %bb21, label %bb29

bb21:                                             ; preds = %bb
  %i22 = load i32**, i32*** %i6, align 8
  %i23 = load i32*, i32** %i22, align 8
  %i24 = bitcast i32* %i23 to i8*
  %i25 = load i32*, i32** %i4, align 8
  %i26 = bitcast i32* %i25 to i8*
  %i27 = load i64, i64* %i7, align 8
  %i28 = mul i64 %i27, 4
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i24, i8* align 4 %i26, i64 %i28, i1 false)
  br label %bb29

bb29:                                             ; preds = %bb21, %bb
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %arg, i32** nonnull align 8 dereferenceable(8) %arg1) #3 {
bb:
  %i = alloca i32**, align 8
  %i2 = alloca i32**, align 8
  %i3 = alloca i32*, align 8
  store i32** %arg, i32*** %i, align 8
  store i32** %arg1, i32*** %i2, align 8
  %i4 = load i32**, i32*** %i, align 8
  %i5 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i4) #12
  %i6 = load i32*, i32** %i5, align 8
  store i32* %i6, i32** %i3, align 8
  %i7 = load i32**, i32*** %i2, align 8
  %i8 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i7) #12
  %i9 = load i32*, i32** %i8, align 8
  %i10 = load i32**, i32*** %i, align 8
  store i32* %i9, i32** %i10, align 8
  %i11 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i3) #12
  %i12 = load i32*, i32** %i11, align 8
  %i13 = load i32**, i32*** %i2, align 8
  store i32* %i12, i32** %i13, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %arg, i64 %arg1) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i3) #12
  %i5 = bitcast i32* %i4 to i8*
  %i6 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i3) #12
  %i7 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %i3) #12
  %i8 = getelementptr inbounds i32, i32* %i6, i64 %i7
  %i9 = bitcast i32* %i8 to i8*
  %i10 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i3) #12
  %i11 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %i3) #12
  %i12 = getelementptr inbounds i32, i32* %i10, i64 %i11
  %i13 = bitcast i32* %i12 to i8*
  %i14 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %i3) #12
  %i15 = load i64, i64* %i2, align 8
  %i16 = getelementptr inbounds i32, i32* %i14, i64 %i15
  %i17 = bitcast i32* %i16 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %i3, i8* %i5, i8* %i9, i8* %i13, i8* %i17) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %arg, i8* %arg1, i8* %arg2, i8* %arg3, i8* %arg4) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i5 = alloca i8*, align 8
  %i6 = alloca i8*, align 8
  %i7 = alloca i8*, align 8
  %i8 = alloca i8*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i8* %arg1, i8** %i5, align 8
  store i8* %arg2, i8** %i6, align 8
  store i8* %arg3, i8** %i7, align 8
  store i8* %arg4, i8** %i8, align 8
  %i9 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %i3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i4 = load i32*, i32** %i3, align 8
  %i5 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i4) #12
  ret i32* %i5
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #9

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %arg) #3 {
bb:
  %i = alloca i32**, align 8
  store i32** %arg, i32*** %i, align 8
  %i1 = load i32**, i32*** %i, align 8
  ret i32** %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %arg) unnamed_addr #3 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %i1) #12
  %i2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 0
  %i3 = load i32*, i32** %i2, align 8
  %i4 = icmp ne i32* %i3, null
  br i1 %i4, label %bb5, label %bb11

bb5:                                              ; preds = %bb
  %i6 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %i1) #12
  %i7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 0
  %i8 = load i32*, i32** %i7, align 8
  %i9 = call i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %i1)
  br label %bb10

bb10:                                             ; preds = %bb5
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i6, i32* %i8, i64 %i9) #12
  br label %bb11

bb11:                                             ; preds = %bb10, %bb
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 1
  %i3 = load i32*, i32** %i2, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %i1, i32* %i3) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i64 %arg2) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i6 = load i32*, i32** %i3, align 8
  %i7 = load i64, i64* %i4, align 8
  call void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %i5, i32* %i6, i64 %i7) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i2 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i1) #12
  %i3 = load i32*, i32** %i2, align 8
  %i4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 0
  %i5 = load i32*, i32** %i4, align 8
  %i6 = ptrtoint i32* %i3 to i64
  %i7 = ptrtoint i32* %i5 to i64
  %i8 = sub i64 %i6, %i7
  %i9 = sdiv exact i64 %i8, 4
  ret i64 %i9
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %arg, i32* %arg1) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"struct.std::__1::integral_constant.3", align 1
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i4 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i5 = load i32*, i32** %i2, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %i4, i32* %i5) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %arg, i32* %arg1) #3 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"struct.std::__1::integral_constant.3", align 1
  %i2 = alloca %"struct.std::__1::__split_buffer"*, align 8
  %i3 = alloca i32*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i2, align 8
  store i32* %arg1, i32** %i3, align 8
  %i4 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i2, align 8
  br label %bb5

bb5:                                              ; preds = %bb16, %bb
  %i6 = load i32*, i32** %i3, align 8
  %i7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i8 = load i32*, i32** %i7, align 8
  %i9 = icmp ne i32* %i6, %i8
  br i1 %i9, label %bb10, label %bb17

bb10:                                             ; preds = %bb5
  %i11 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %i4) #12
  %i12 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i13 = load i32*, i32** %i12, align 8
  %i14 = getelementptr inbounds i32, i32* %i13, i32 -1
  store i32* %i14, i32** %i12, align 8
  %i15 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i14) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i11, i32* %i15)
  br label %bb16

bb16:                                             ; preds = %bb10
  br label %bb5

bb17:                                             ; preds = %bb5
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"struct.std::__1::integral_constant", align 1
  %i4 = alloca %"struct.std::__1::__has_destroy", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i5 = bitcast %"struct.std::__1::__has_destroy"* %i4 to %"struct.std::__1::integral_constant"*
  %i6 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i7 = load i32*, i32** %i2, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i6, i32* %i7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1) #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %i2 = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i2, align 8
  store i32* %arg1, i32** %i3, align 8
  %i4 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i2, align 8
  %i5 = load i32*, i32** %i3, align 8
  call void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %i4, i32* %i5)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %arg, i32* %arg1) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %arg, i32* %arg1, i64 %arg2) #3 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i6 = load i32*, i32** %i3, align 8
  %i7 = bitcast i32* %i6 to i8*
  %i8 = load i64, i64* %i4, align 8
  %i9 = mul i64 %i8, 4
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %i7, i64 %i9, i64 4)
  br label %bb10

bb10:                                             ; preds = %bb
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %arg, i64 %arg1, i64 %arg2) #0 {
bb:
  %i = alloca i8*, align 8
  %i3 = alloca i64, align 8
  %i4 = alloca i64, align 8
  store i8* %arg, i8** %i, align 8
  store i64 %arg1, i64* %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load i8*, i8** %i, align 8
  %i6 = load i64, i64* %i3, align 8
  %i7 = load i64, i64* %i4, align 8
  call void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %i5, i64 %i6, i64 %i7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %arg, i64 %arg1, i64 %arg2) #0 align 2 {
bb:
  %i = alloca i8*, align 8
  %i3 = alloca i64, align 8
  %i4 = alloca i64, align 8
  store i8* %arg, i8** %i, align 8
  store i64 %arg1, i64* %i3, align 8
  store i64 %arg2, i64* %i4, align 8
  %i5 = load i8*, i8** %i, align 8
  %i6 = load i64, i64* %i3, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %i5, i64 %i6)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %arg, i64 %arg1) #0 align 2 {
bb:
  %i = alloca i8*, align 8
  %i2 = alloca i64, align 8
  store i8* %arg, i8** %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load i8*, i8** %i, align 8
  call void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %i3)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %arg) #3 align 2 {
bb:
  %i = alloca i8*, align 8
  store i8* %arg, i8** %i, align 8
  %i1 = load i8*, i8** %i, align 8
  call void @_ZdlPv(i8* %i1) #15
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) #10

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %arg) #3 align 2 {
bb:
  %i = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %i, align 8
  %i1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %i, align 8
  %i2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i1, i32 0, i32 3
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %arg) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %i, align 8
  %i2 = bitcast %"class.std::__1::__compressed_pair.1"* %i1 to %"struct.std::__1::__compressed_pair_elem"*
  %i3 = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i2) #12
  ret i32** %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %arg, i64 %arg1) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i64 %arg1, i64* %i2, align 8
  %i3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i4 = bitcast %"class.std::__1::vector"* %i3 to %"class.std::__1::__vector_base"*
  %i5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i4, i32 0, i32 0
  %i6 = load i32*, i32** %i5, align 8
  %i7 = load i64, i64* %i2, align 8
  %i8 = getelementptr inbounds i32, i32* %i6, i64 %i7
  ret i32* %i8
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", align 8
  %i4 = alloca i8*, align 8
  %i5 = alloca i32, align 4
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i6 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i6, i64 1)
  %i7 = bitcast %"class.std::__1::vector"* %i6 to %"class.std::__1::__vector_base"*
  %i8 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i7) #12
  %i9 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, i32 0, i32 1
  %i10 = load i32*, i32** %i9, align 8
  %i11 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i10) #12
  %i12 = load i32*, i32** %i2, align 8
  %i13 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i12) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i8, i32* %i11, i32* nonnull align 4 dereferenceable(4) %i13)
  br label %bb14

bb14:                                             ; preds = %bb
  %i15 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3, i32 0, i32 1
  %i16 = load i32*, i32** %i15, align 8
  %i17 = getelementptr inbounds i32, i32* %i16, i32 1
  store i32* %i17, i32** %i15, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %i3) #12
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %i = alloca %"class.std::__1::vector"*, align 8
  %i2 = alloca i32*, align 8
  %i3 = alloca %"class.std::__1::allocator"*, align 8
  %i4 = alloca %"struct.std::__1::__split_buffer", align 8
  %i5 = alloca i8*, align 8
  %i6 = alloca i32, align 4
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %i, align 8
  %i8 = bitcast %"class.std::__1::vector"* %i7 to %"class.std::__1::__vector_base"*
  %i9 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i8) #12
  store %"class.std::__1::allocator"* %i9, %"class.std::__1::allocator"** %i3, align 8
  %i10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i7) #12
  %i11 = add i64 %i10, 1
  %i12 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %i7, i64 %i11)
  %i13 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i7) #12
  %i14 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %i4, i64 %i12, i64 %i13, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i14)
  %i15 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  %i16 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i17 = load i32*, i32** %i16, align 8
  %i18 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i17) #12
  %i19 = load i32*, i32** %i2, align 8
  %i20 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i19) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i15, i32* %i18, i32* nonnull align 4 dereferenceable(4) %i20)
  br label %bb21

bb21:                                             ; preds = %bb
  %i22 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i4, i32 0, i32 2
  %i23 = load i32*, i32** %i22, align 8
  %i24 = getelementptr inbounds i32, i32* %i23, i32 1
  store i32* %i24, i32** %i22, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %i7, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %i4)
  br label %bb25

bb25:                                             ; preds = %bb21
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %i4) #12
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #0 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca %"struct.std::__1::integral_constant", align 1
  %i6 = alloca %"struct.std::__1::__has_construct.4", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i7 = bitcast %"struct.std::__1::__has_construct.4"* %i6 to %"struct.std::__1::integral_constant"*
  %i8 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i9 = load i32*, i32** %i3, align 8
  %i10 = load i32*, i32** %i4, align 8
  %i11 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i10) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i8, i32* %i9, i32* nonnull align 4 dereferenceable(4) %i11)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %arg) #3 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #0 align 2 {
bb:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %i3 = alloca %"class.std::__1::allocator"*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i3, align 8
  store i32* %arg1, i32** %i4, align 8
  store i32* %arg2, i32** %i5, align 8
  %i6 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i3, align 8
  %i7 = load i32*, i32** %i4, align 8
  %i8 = load i32*, i32** %i5, align 8
  %i9 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i8) #12
  call void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %i6, i32* %i7, i32* nonnull align 4 dereferenceable(4) %i9)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %arg, i32* %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) #3 align 2 {
bb:
  %i = alloca %"class.std::__1::allocator"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %i, align 8
  %i6 = load i32*, i32** %i3, align 8
  %i7 = bitcast i32* %i6 to i8*
  %i8 = bitcast i8* %i7 to i32*
  %i9 = load i32*, i32** %i4, align 8
  %i10 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i9) #12
  %i11 = load i32, i32* %i10, align 4
  store i32 %i11, i32* %i8, align 4
  ret void
}

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { argmemonly nounwind willreturn writeonly }
attributes #3 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noinline noreturn nounwind }
attributes #5 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { noinline noreturn optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { argmemonly nounwind willreturn }
attributes #10 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #11 = { builtin allocsize(0) }
attributes #12 = { nounwind }
attributes #13 = { noreturn nounwind }
attributes #14 = { noreturn }
attributes #15 = { builtin nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
