; ModuleID = 'vector1.llc'
source_filename = "vector1.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }
%"struct.std::__1::__default_init_tag" = type { i8 }
%"class.std::__1::__vector_base_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.0" = type { i8 }
%"class.std::__1::allocator" = type { i8 }
%"struct.std::__1::integral_constant" = type { i8 }
%"struct.std::__1::__has_destroy" = type { i8 }
%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction" = type { %"class.std::__1::vector"*, i32*, i32* }
%"struct.std::__1::__split_buffer" = type { i32*, i32*, i32*, %"class.std::__1::__compressed_pair.1" }
%"class.std::__1::__compressed_pair.1" = type { %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem.2" }
%"struct.std::__1::__compressed_pair_elem.2" = type { %"class.std::__1::allocator"* }
%"struct.std::__1::__has_construct" = type { i8 }
%"struct.std::__1::__less" = type { i8 }
%"struct.std::__1::__has_max_size" = type { i8 }
%"class.std::__1::__split_buffer_common" = type { i8 }
%"class.std::length_error" = type { %"class.std::logic_error" }
%"class.std::logic_error" = type { %"class.std::exception", %"class.std::__1::__libcpp_refstring" }
%"class.std::exception" = type { i32 (...)** }
%"class.std::__1::__libcpp_refstring" = type { i8* }
%"struct.std::__1::integral_constant.3" = type { i8 }

@.str = private unnamed_addr constant [68 x i8] c"allocator<T>::allocate(size_t n) 'n' exceeds maximum supported size\00", align 1
@_ZTISt12length_error = external constant i8*
@_ZTVSt12length_error = external unnamed_addr constant { [5 x i8*] }, align 8

; Function Attrs: noinline optnone ssp uwtable
define void @_Z4testNSt3__16vectorIiNS_9allocatorIiEEEE(%"class.std::__1::vector"* noalias sret %arg, %"class.std::__1::vector"* %arg1) #0 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca i8*, align 8
  %tmp2 = alloca i1, align 1
  %tmp3 = alloca i32, align 4
  %tmp4 = alloca i8*
  %tmp5 = alloca i32
  %tmp6 = bitcast %"class.std::__1::vector"* %arg to i8*
  store i8* %tmp6, i8** %tmp, align 8
  store i1 false, i1* %tmp2, align 1
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %arg) #10
  store i32 0, i32* %tmp3, align 4
  br label %bb7

bb7:                                              ; preds = %bb17, %bb
  %tmp8 = load i32, i32* %tmp3, align 4
  %tmp9 = sext i32 %tmp8 to i64
  %tmp10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %arg1) #10
  %tmp11 = icmp ult i64 %tmp9, %tmp10
  br i1 %tmp11, label %bb12, label %bb20

bb12:                                             ; preds = %bb7
  %tmp13 = load i32, i32* %tmp3, align 4
  %tmp14 = sext i32 %tmp13 to i64
  %tmp15 = call dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %arg1, i64 %tmp14) #10
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector"* %arg, i32* dereferenceable(4) %tmp15)
  br label %bb16

bb16:                                             ; preds = %bb12
  br label %bb17

bb17:                                             ; preds = %bb16
  %tmp18 = load i32, i32* %tmp3, align 4
  %tmp19 = add nsw i32 %tmp18, 1
  store i32 %tmp19, i32* %tmp3, align 4
  br label %bb7

bb20:                                             ; preds = %bb7
  store i1 true, i1* %tmp2, align 1
  %tmp21 = load i1, i1* %tmp2, align 1
  br i1 %tmp21, label %bb23, label %bb22

bb22:                                             ; preds = %bb20
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector"* %arg) #10
  br label %bb23

bb23:                                             ; preds = %bb22, %bb20
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %tmp1) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  %tmp3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp2, i32 0, i32 1
  %tmp4 = load i32*, i32** %tmp3, align 8
  %tmp5 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  %tmp6 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp5, i32 0, i32 0
  %tmp7 = load i32*, i32** %tmp6, align 8
  %tmp8 = ptrtoint i32* %tmp4 to i64
  %tmp9 = ptrtoint i32* %tmp7 to i64
  %tmp10 = sub i64 %tmp8, %tmp9
  %tmp11 = sdiv exact i64 %tmp10, 4
  ret i64 %tmp11
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector"* %arg, i32* dereferenceable(4) %arg1) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca i32*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp4 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp4, i32 0, i32 1
  %tmp6 = load i32*, i32** %tmp5, align 8
  %tmp7 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp8 = call dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %tmp7) #10
  %tmp9 = load i32*, i32** %tmp8, align 8
  %tmp10 = icmp ne i32* %tmp6, %tmp9
  br i1 %tmp10, label %bb11, label %bb13

bb11:                                             ; preds = %bb
  %tmp12 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector"* %tmp3, i32* dereferenceable(4) %tmp12)
  br label %bb15

bb13:                                             ; preds = %bb
  %tmp14 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector"* %tmp3, i32* dereferenceable(4) %tmp14)
  br label %bb15

bb15:                                             ; preds = %bb13, %bb11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %arg, i64 %arg1) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i64 %arg1, i64* %tmp2, align 8
  %tmp3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp4 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp4, i32 0, i32 0
  %tmp6 = load i32*, i32** %tmp5, align 8
  %tmp7 = load i64, i64* %tmp2, align 8
  %tmp8 = getelementptr inbounds i32, i32* %tmp6, i64 %tmp7
  ret i32* %tmp8
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector"* %tmp1) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %tmp2) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %arg) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  %tmp1 = alloca i8*, align 8
  %tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp3 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp4 = bitcast %"class.std::__1::__vector_base"* %tmp3 to %"class.std::__1::__vector_base_common"*
  call void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %tmp4)
  br label %bb5

bb5:                                              ; preds = %bb
  %tmp6 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp3, i32 0, i32 0
  store i32* null, i32** %tmp6, align 8
  %tmp7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp3, i32 0, i32 1
  store i32* null, i32** %tmp7, align 8
  %tmp8 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp3, i32 0, i32 2
  store i8* null, i8** %tmp1, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %tmp8, i8** dereferenceable(8) %tmp1, %"struct.std::__1::__default_init_tag"* dereferenceable(1) %tmp2)
  br label %bb9

bb9:                                              ; preds = %bb5
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base_common"*, align 8
  store %"class.std::__1::__vector_base_common"* %arg, %"class.std::__1::__vector_base_common"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base_common"*, %"class.std::__1::__vector_base_common"** %tmp, align 8
  ret void
}

; Function Attrs: noinline noreturn nounwind
define linkonce_odr hidden void @__clang_call_terminate(i8* %arg) #2 {
bb:
  %tmp = call i8* @__cxa_begin_catch(i8* %arg) #10
  call void @_ZSt9terminatev() #11
  unreachable
}

declare i8* @__cxa_begin_catch(i8*)

declare void @_ZSt9terminatev()

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %arg, i8** dereferenceable(8) %arg1, %"struct.std::__1::__default_init_tag"* dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  %tmp3 = alloca i8**, align 8
  %tmp4 = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  store i8** %arg1, i8*** %tmp3, align 8
  store %"struct.std::__1::__default_init_tag"* %arg2, %"struct.std::__1::__default_init_tag"** %tmp4, align 8
  %tmp5 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp6 = load i8**, i8*** %tmp3, align 8
  %tmp7 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %tmp4, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %tmp5, i8** dereferenceable(8) %tmp6, %"struct.std::__1::__default_init_tag"* dereferenceable(1) %tmp7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %arg, i8** dereferenceable(8) %arg1, %"struct.std::__1::__default_init_tag"* dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  %tmp3 = alloca i8**, align 8
  %tmp4 = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %tmp5 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  store i8** %arg1, i8*** %tmp3, align 8
  store %"struct.std::__1::__default_init_tag"* %arg2, %"struct.std::__1::__default_init_tag"** %tmp4, align 8
  %tmp6 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp7 = bitcast %"class.std::__1::__compressed_pair"* %tmp6 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp8 = load i8**, i8*** %tmp3, align 8
  %tmp9 = call dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** dereferenceable(8) %tmp8) #10
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %tmp7, i8** dereferenceable(8) %tmp9)
  %tmp10 = bitcast %"class.std::__1::__compressed_pair"* %tmp6 to %"struct.std::__1::__compressed_pair_elem.0"*
  %tmp11 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %tmp4, align 8
  %tmp12 = call dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* dereferenceable(1) %tmp11) #10
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %tmp10)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** dereferenceable(8) %arg) #1 {
bb:
  %tmp = alloca i8**, align 8
  store i8** %arg, i8*** %tmp, align 8
  %tmp1 = load i8**, i8*** %tmp, align 8
  ret i8** %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %arg, i8** dereferenceable(8) %arg1) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  %tmp2 = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  store i8** %arg1, i8*** %tmp2, align 8
  %tmp3 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  %tmp4 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %tmp3, i32 0, i32 0
  %tmp5 = load i8**, i8*** %tmp2, align 8
  %tmp6 = call dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** dereferenceable(8) %tmp5) #10
  store i32* null, i32** %tmp4, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* dereferenceable(1) %arg) #1 {
bb:
  %tmp = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"struct.std::__1::__default_init_tag"* %arg, %"struct.std::__1::__default_init_tag"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %tmp, align 8
  ret %"struct.std::__1::__default_init_tag"* %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  %tmp1 = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %tmp1, align 8
  %tmp2 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %tmp1, align 8
  %tmp3 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %tmp2 to %"class.std::__1::allocator"*
  call void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %tmp3) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  %tmp1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp2 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base"* %tmp2) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp3 = bitcast i32* %tmp2 to i8*
  %tmp4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp6 = getelementptr inbounds i32, i32* %tmp4, i64 %tmp5
  %tmp7 = bitcast i32* %tmp6 to i8*
  %tmp8 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp9 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp10 = getelementptr inbounds i32, i32* %tmp8, i64 %tmp9
  %tmp11 = bitcast i32* %tmp10 to i8*
  %tmp12 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp13 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %tmp1) #10
  %tmp14 = getelementptr inbounds i32, i32* %tmp12, i64 %tmp13
  %tmp15 = bitcast i32* %tmp14 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %tmp1, i8* %tmp3, i8* %tmp7, i8* %tmp11, i8* %tmp15) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 0
  %tmp3 = load i32*, i32** %tmp2, align 8
  %tmp4 = icmp ne i32* %tmp3, null
  br i1 %tmp4, label %bb5, label %bb10

bb5:                                              ; preds = %bb
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base"* %tmp1) #10
  %tmp6 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp1) #10
  %tmp7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 0
  %tmp8 = load i32*, i32** %tmp7, align 8
  %tmp9 = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %tmp1) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* dereferenceable(1) %tmp6, i32* %tmp8, i64 %tmp9) #10
  br label %bb10

bb10:                                             ; preds = %bb5, %bb
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %arg, i8* %arg1, i8* %arg2, i8* %arg3, i8* %arg4) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp5 = alloca i8*, align 8
  %tmp6 = alloca i8*, align 8
  %tmp7 = alloca i8*, align 8
  %tmp8 = alloca i8*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i8* %arg1, i8** %tmp5, align 8
  store i8* %arg2, i8** %tmp6, align 8
  store i8* %arg3, i8** %tmp7, align 8
  store i8* %arg4, i8** %tmp8, align 8
  %tmp9 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  %tmp3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp2, i32 0, i32 0
  %tmp4 = load i32*, i32** %tmp3, align 8
  %tmp5 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %tmp4) #10
  ret i32* %tmp5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::vector"* %tmp1 to %"class.std::__1::__vector_base"*
  %tmp3 = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %tmp2) #10
  ret i64 %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %arg) #1 {
bb:
  %tmp = alloca i32*, align 8
  store i32* %arg, i32** %tmp, align 8
  %tmp1 = load i32*, i32** %tmp, align 8
  ret i32* %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = call dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %tmp1) #10
  %tmp3 = load i32*, i32** %tmp2, align 8
  %tmp4 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 0
  %tmp5 = load i32*, i32** %tmp4, align 8
  %tmp6 = ptrtoint i32* %tmp3 to i64
  %tmp7 = ptrtoint i32* %tmp5 to i64
  %tmp8 = sub i64 %tmp6, %tmp7
  %tmp9 = sdiv exact i64 %tmp8, 4
  ret i64 %tmp9
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 2
  %tmp3 = call dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair"* %tmp1 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp3 = call dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %tmp1, i32 0, i32 0
  ret i32** %tmp2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 0
  %tmp3 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base"* %tmp1, i32* %tmp3) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1, i64 %arg2) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i32*, align 8
  %tmp4 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp6 = load i32*, i32** %tmp3, align 8
  %tmp7 = load i64, i64* %tmp4, align 8
  call void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %tmp5, i32* %tmp6, i64 %tmp7) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 2
  %tmp3 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %tmp2) #10
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base"* %arg, i32* %arg1) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  %tmp2 = alloca i32*, align 8
  %tmp3 = alloca i32*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp4 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp4, i32 0, i32 1
  %tmp6 = load i32*, i32** %tmp5, align 8
  store i32* %tmp6, i32** %tmp3, align 8
  br label %bb7

bb7:                                              ; preds = %bb16, %bb
  %tmp8 = load i32*, i32** %tmp2, align 8
  %tmp9 = load i32*, i32** %tmp3, align 8
  %tmp10 = icmp ne i32* %tmp8, %tmp9
  br i1 %tmp10, label %bb11, label %bb17

bb11:                                             ; preds = %bb7
  %tmp12 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp4) #10
  %tmp13 = load i32*, i32** %tmp3, align 8
  %tmp14 = getelementptr inbounds i32, i32* %tmp13, i32 -1
  store i32* %tmp14, i32** %tmp3, align 8
  %tmp15 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %tmp14) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* dereferenceable(1) %tmp12, i32* %tmp15)
  br label %bb16

bb16:                                             ; preds = %bb11
  br label %bb7

bb17:                                             ; preds = %bb7
  %tmp18 = load i32*, i32** %tmp2, align 8
  %tmp19 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp4, i32 0, i32 1
  store i32* %tmp18, i32** %tmp19, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp2 = alloca i32*, align 8
  %tmp3 = alloca %"struct.std::__1::integral_constant", align 1
  %tmp4 = alloca %"struct.std::__1::__has_destroy", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp5 = bitcast %"struct.std::__1::__has_destroy"* %tmp4 to %"struct.std::__1::integral_constant"*
  %tmp6 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp7 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* dereferenceable(1) %tmp6, i32* %tmp7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1) #0 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::integral_constant", align 1
  %tmp2 = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp2, align 8
  store i32* %arg1, i32** %tmp3, align 8
  %tmp4 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp2, align 8
  %tmp5 = load i32*, i32** %tmp3, align 8
  call void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %tmp4, i32* %tmp5)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %arg, i32* %arg1) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp2 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %arg, i32* %arg1, i64 %arg2) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i32*, align 8
  %tmp4 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp6 = load i32*, i32** %tmp3, align 8
  %tmp7 = bitcast i32* %tmp6 to i8*
  %tmp8 = load i64, i64* %tmp4, align 8
  %tmp9 = mul i64 %tmp8, 4
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %tmp7, i64 %tmp9, i64 4)
  br label %bb10

bb10:                                             ; preds = %bb
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %arg, i64 %arg1, i64 %arg2) #0 {
bb:
  %tmp = alloca i8*, align 8
  %tmp3 = alloca i64, align 8
  %tmp4 = alloca i64, align 8
  store i8* %arg, i8** %tmp, align 8
  store i64 %arg1, i64* %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load i8*, i8** %tmp, align 8
  %tmp6 = load i64, i64* %tmp3, align 8
  %tmp7 = load i64, i64* %tmp4, align 8
  call void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %tmp5, i64 %tmp6, i64 %tmp7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %arg, i64 %arg1, i64 %arg2) #0 align 2 {
bb:
  %tmp = alloca i8*, align 8
  %tmp3 = alloca i64, align 8
  %tmp4 = alloca i64, align 8
  store i8* %arg, i8** %tmp, align 8
  store i64 %arg1, i64* %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load i8*, i8** %tmp, align 8
  %tmp6 = load i64, i64* %tmp3, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %tmp5, i64 %tmp6)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %arg, i64 %arg1) #0 align 2 {
bb:
  %tmp = alloca i8*, align 8
  %tmp2 = alloca i64, align 8
  store i8* %arg, i8** %tmp, align 8
  store i64 %arg1, i64* %tmp2, align 8
  %tmp3 = load i8*, i8** %tmp, align 8
  call void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %tmp3)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %arg) #1 align 2 {
bb:
  %tmp = alloca i8*, align 8
  store i8* %arg, i8** %tmp, align 8
  %tmp1 = load i8*, i8** %tmp, align 8
  call void @_ZdlPv(i8* %tmp1) #12
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) #3

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair"* %tmp1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %tmp3 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %tmp2) #10
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %tmp, align 8
  %tmp2 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %tmp1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %tmp2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 2
  %tmp3 = call dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector"* %arg, i32* dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca i32*, align 8
  %tmp3 = alloca %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", align 8
  %tmp4 = alloca i8*
  %tmp5 = alloca i32
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp6 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp3, %"class.std::__1::vector"* dereferenceable(24) %tmp6, i64 1)
  %tmp7 = bitcast %"class.std::__1::vector"* %tmp6 to %"class.std::__1::__vector_base"*
  %tmp8 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp7) #10
  %tmp9 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp3, i32 0, i32 1
  %tmp10 = load i32*, i32** %tmp9, align 8
  %tmp11 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %tmp10) #10
  %tmp12 = load i32*, i32** %tmp2, align 8
  %tmp13 = call dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %tmp12) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* dereferenceable(1) %tmp8, i32* %tmp11, i32* dereferenceable(4) %tmp13)
  br label %bb14

bb14:                                             ; preds = %bb
  %tmp15 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp3, i32 0, i32 1
  %tmp16 = load i32*, i32** %tmp15, align 8
  %tmp17 = getelementptr inbounds i32, i32* %tmp16, i32 1
  store i32* %tmp17, i32** %tmp15, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp3) #10
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector"* %arg, i32* dereferenceable(4) %arg1) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca i32*, align 8
  %tmp3 = alloca %"class.std::__1::allocator"*, align 8
  %tmp4 = alloca %"struct.std::__1::__split_buffer", align 8
  %tmp5 = alloca i8*
  %tmp6 = alloca i32
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp8 = bitcast %"class.std::__1::vector"* %tmp7 to %"class.std::__1::__vector_base"*
  %tmp9 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp8) #10
  store %"class.std::__1::allocator"* %tmp9, %"class.std::__1::allocator"** %tmp3, align 8
  %tmp10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %tmp7) #10
  %tmp11 = add i64 %tmp10, 1
  %tmp12 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %tmp7, i64 %tmp11)
  %tmp13 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %tmp7) #10
  %tmp14 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp3, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %tmp4, i64 %tmp12, i64 %tmp13, %"class.std::__1::allocator"* dereferenceable(1) %tmp14)
  %tmp15 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp3, align 8
  %tmp16 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp4, i32 0, i32 2
  %tmp17 = load i32*, i32** %tmp16, align 8
  %tmp18 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %tmp17) #10
  %tmp19 = load i32*, i32** %tmp2, align 8
  %tmp20 = call dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %tmp19) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* dereferenceable(1) %tmp15, i32* %tmp18, i32* dereferenceable(4) %tmp20)
  br label %bb21

bb21:                                             ; preds = %bb
  %tmp22 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp4, i32 0, i32 2
  %tmp23 = load i32*, i32** %tmp22, align 8
  %tmp24 = getelementptr inbounds i32, i32* %tmp23, i32 1
  store i32* %tmp24, i32** %tmp22, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %tmp7, %"struct.std::__1::__split_buffer"* dereferenceable(40) %tmp4)
  br label %bb25

bb25:                                             ; preds = %bb21
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %tmp4) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair"* %tmp1 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp3 = call dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %arg, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %tmp1, i32 0, i32 0
  ret i32** %tmp2
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"class.std::__1::vector"* dereferenceable(24) %arg1, i64 %arg2) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, align 8
  %tmp3 = alloca %"class.std::__1::vector"*, align 8
  %tmp4 = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  store %"class.std::__1::vector"* %arg1, %"class.std::__1::vector"** %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  %tmp6 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp3, align 8
  %tmp7 = load i64, i64* %tmp4, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp5, %"class.std::__1::vector"* dereferenceable(24) %tmp6, i64 %tmp7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1, i32* dereferenceable(4) %arg2) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i32*, align 8
  %tmp4 = alloca i32*, align 8
  %tmp5 = alloca %"struct.std::__1::integral_constant", align 1
  %tmp6 = alloca %"struct.std::__1::__has_construct", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp3, align 8
  store i32* %arg2, i32** %tmp4, align 8
  %tmp7 = bitcast %"struct.std::__1::__has_construct"* %tmp6 to %"struct.std::__1::integral_constant"*
  %tmp8 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp9 = load i32*, i32** %tmp3, align 8
  %tmp10 = load i32*, i32** %tmp4, align 8
  %tmp11 = call dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %tmp10) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* dereferenceable(1) %tmp8, i32* %tmp9, i32* dereferenceable(4) %tmp11)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %arg) #1 {
bb:
  %tmp = alloca i32*, align 8
  store i32* %arg, i32** %tmp, align 8
  %tmp1 = load i32*, i32** %tmp, align 8
  ret i32* %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp1) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"class.std::__1::vector"* dereferenceable(24) %arg1, i64 %arg2) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, align 8
  %tmp3 = alloca %"class.std::__1::vector"*, align 8
  %tmp4 = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  store %"class.std::__1::vector"* %arg1, %"class.std::__1::vector"** %tmp3, align 8
  store i64 %arg2, i64* %tmp4, align 8
  %tmp5 = load %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  %tmp6 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp5, i32 0, i32 0
  %tmp7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp3, align 8
  store %"class.std::__1::vector"* %tmp7, %"class.std::__1::vector"** %tmp6, align 8
  %tmp8 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp5, i32 0, i32 1
  %tmp9 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp3, align 8
  %tmp10 = bitcast %"class.std::__1::vector"* %tmp9 to %"class.std::__1::__vector_base"*
  %tmp11 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp10, i32 0, i32 1
  %tmp12 = load i32*, i32** %tmp11, align 8
  store i32* %tmp12, i32** %tmp8, align 8
  %tmp13 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp5, i32 0, i32 2
  %tmp14 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp3, align 8
  %tmp15 = bitcast %"class.std::__1::vector"* %tmp14 to %"class.std::__1::__vector_base"*
  %tmp16 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp15, i32 0, i32 1
  %tmp17 = load i32*, i32** %tmp16, align 8
  %tmp18 = load i64, i64* %tmp4, align 8
  %tmp19 = getelementptr inbounds i32, i32* %tmp17, i64 %tmp18
  store i32* %tmp19, i32** %tmp13, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1, i32* dereferenceable(4) %arg2) #0 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::integral_constant", align 1
  %tmp3 = alloca %"class.std::__1::allocator"*, align 8
  %tmp4 = alloca i32*, align 8
  %tmp5 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp3, align 8
  store i32* %arg1, i32** %tmp4, align 8
  store i32* %arg2, i32** %tmp5, align 8
  %tmp6 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp3, align 8
  %tmp7 = load i32*, i32** %tmp4, align 8
  %tmp8 = load i32*, i32** %tmp5, align 8
  %tmp9 = call dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %tmp8) #10
  call void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %tmp6, i32* %tmp7, i32* dereferenceable(4) %tmp9)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %arg, i32* %arg1, i32* dereferenceable(4) %arg2) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i32*, align 8
  %tmp4 = alloca i32*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp3, align 8
  store i32* %arg2, i32** %tmp4, align 8
  %tmp5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp6 = load i32*, i32** %tmp3, align 8
  %tmp7 = bitcast i32* %tmp6 to i8*
  %tmp8 = bitcast i8* %tmp7 to i32*
  %tmp9 = load i32*, i32** %tmp4, align 8
  %tmp10 = call dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* dereferenceable(4) %tmp9) #10
  %tmp11 = load i32, i32* %tmp10, align 4
  store i32 %tmp11, i32* %tmp8, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %arg, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp1, i32 0, i32 1
  %tmp3 = load i32*, i32** %tmp2, align 8
  %tmp4 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int> >::_ConstructTransaction"* %tmp1, i32 0, i32 0
  %tmp5 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp4, align 8
  %tmp6 = bitcast %"class.std::__1::vector"* %tmp5 to %"class.std::__1::__vector_base"*
  %tmp7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp6, i32 0, i32 1
  store i32* %tmp3, i32** %tmp7, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %arg, i64 %arg1) #0 align 2 {
bb:
  %tmp = alloca i64, align 8
  %tmp2 = alloca %"class.std::__1::vector"*, align 8
  %tmp3 = alloca i64, align 8
  %tmp4 = alloca i64, align 8
  %tmp5 = alloca i64, align 8
  %tmp6 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp2, align 8
  store i64 %arg1, i64* %tmp3, align 8
  %tmp7 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp2, align 8
  %tmp8 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %tmp7) #10
  store i64 %tmp8, i64* %tmp4, align 8
  %tmp9 = load i64, i64* %tmp3, align 8
  %tmp10 = load i64, i64* %tmp4, align 8
  %tmp11 = icmp ugt i64 %tmp9, %tmp10
  br i1 %tmp11, label %bb12, label %bb14

bb12:                                             ; preds = %bb
  %tmp13 = bitcast %"class.std::__1::vector"* %tmp7 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %tmp13) #13
  unreachable

bb14:                                             ; preds = %bb
  %tmp15 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %tmp7) #10
  store i64 %tmp15, i64* %tmp5, align 8
  %tmp16 = load i64, i64* %tmp5, align 8
  %tmp17 = load i64, i64* %tmp4, align 8
  %tmp18 = udiv i64 %tmp17, 2
  %tmp19 = icmp uge i64 %tmp16, %tmp18
  br i1 %tmp19, label %bb20, label %bb22

bb20:                                             ; preds = %bb14
  %tmp21 = load i64, i64* %tmp4, align 8
  store i64 %tmp21, i64* %tmp, align 8
  br label %bb27

bb22:                                             ; preds = %bb14
  %tmp23 = load i64, i64* %tmp5, align 8
  %tmp24 = mul i64 2, %tmp23
  store i64 %tmp24, i64* %tmp6, align 8
  %tmp25 = call dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* dereferenceable(8) %tmp6, i64* dereferenceable(8) %tmp3)
  %tmp26 = load i64, i64* %tmp25, align 8
  store i64 %tmp26, i64* %tmp, align 8
  br label %bb27

bb27:                                             ; preds = %bb22, %bb20
  %tmp28 = load i64, i64* %tmp, align 8
  ret i64 %tmp28
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %arg, i64 %arg1, i64 %arg2, %"class.std::__1::allocator"* dereferenceable(1) %arg3) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  %tmp4 = alloca i64, align 8
  %tmp5 = alloca i64, align 8
  %tmp6 = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  store i64 %arg1, i64* %tmp4, align 8
  store i64 %arg2, i64* %tmp5, align 8
  store %"class.std::__1::allocator"* %arg3, %"class.std::__1::allocator"** %tmp6, align 8
  %tmp7 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp8 = load i64, i64* %tmp4, align 8
  %tmp9 = load i64, i64* %tmp5, align 8
  %tmp10 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp6, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %tmp7, i64 %tmp8, i64 %tmp9, %"class.std::__1::allocator"* dereferenceable(1) %tmp10)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %arg, %"struct.std::__1::__split_buffer"* dereferenceable(40) %arg1) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store %"struct.std::__1::__split_buffer"* %arg1, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp4 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp5 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp4) #10
  %tmp6 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp7 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp6, i32 0, i32 0
  %tmp8 = load i32*, i32** %tmp7, align 8
  %tmp9 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp10 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp9, i32 0, i32 1
  %tmp11 = load i32*, i32** %tmp10, align 8
  %tmp12 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp13 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp12, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* dereferenceable(1) %tmp5, i32* %tmp8, i32* %tmp11, i32** dereferenceable(8) %tmp13)
  %tmp14 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp15 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp14, i32 0, i32 0
  %tmp16 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp17 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp16, i32 0, i32 1
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** dereferenceable(8) %tmp15, i32** dereferenceable(8) %tmp17) #10
  %tmp18 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp19 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp18, i32 0, i32 1
  %tmp20 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp21 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp20, i32 0, i32 2
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** dereferenceable(8) %tmp19, i32** dereferenceable(8) %tmp21) #10
  %tmp22 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp23 = call dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %tmp22) #10
  %tmp24 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp25 = call dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %tmp24) #10
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** dereferenceable(8) %tmp23, i32** dereferenceable(8) %tmp25) #10
  %tmp26 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp27 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp26, i32 0, i32 1
  %tmp28 = load i32*, i32** %tmp27, align 8
  %tmp29 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  %tmp30 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp29, i32 0, i32 0
  store i32* %tmp28, i32** %tmp30, align 8
  %tmp31 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %tmp3) #10
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %tmp3, i64 %tmp31) #10
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %tmp3)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %arg) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %tmp1) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %arg) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp1 = alloca i64, align 8
  %tmp2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp4 = bitcast %"class.std::__1::vector"* %tmp3 to %"class.std::__1::__vector_base"*
  %tmp5 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %tmp4) #10
  %tmp6 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* dereferenceable(1) %tmp5) #10
  store i64 %tmp6, i64* %tmp1, align 8
  %tmp7 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #10
  store i64 %tmp7, i64* %tmp2, align 8
  %tmp8 = call dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* dereferenceable(8) %tmp1, i64* dereferenceable(8) %tmp2)
  br label %bb9

bb9:                                              ; preds = %bb
  %tmp10 = load i64, i64* %tmp8, align 8
  ret i64 %tmp10
}

; Function Attrs: noreturn
declare void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"*) #4

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* dereferenceable(8) %arg, i64* dereferenceable(8) %arg1) #0 {
bb:
  %tmp = alloca i64*, align 8
  %tmp2 = alloca i64*, align 8
  %tmp3 = alloca %"struct.std::__1::__less", align 1
  store i64* %arg, i64** %tmp, align 8
  store i64* %arg1, i64** %tmp2, align 8
  %tmp4 = load i64*, i64** %tmp, align 8
  %tmp5 = load i64*, i64** %tmp2, align 8
  %tmp6 = call dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* dereferenceable(8) %tmp4, i64* dereferenceable(8) %tmp5)
  ret i64* %tmp6
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* dereferenceable(8) %arg, i64* dereferenceable(8) %arg1) #0 {
bb:
  %tmp = alloca i64*, align 8
  %tmp2 = alloca i64*, align 8
  %tmp3 = alloca %"struct.std::__1::__less", align 1
  store i64* %arg, i64** %tmp, align 8
  store i64* %arg1, i64** %tmp2, align 8
  %tmp4 = load i64*, i64** %tmp, align 8
  %tmp5 = load i64*, i64** %tmp2, align 8
  %tmp6 = call dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* dereferenceable(8) %tmp4, i64* dereferenceable(8) %tmp5)
  ret i64* %tmp6
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* dereferenceable(1) %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp1 = alloca %"struct.std::__1::integral_constant", align 1
  %tmp2 = alloca %"struct.std::__1::__has_max_size", align 1
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  %tmp3 = bitcast %"struct.std::__1::__has_max_size"* %tmp2 to %"struct.std::__1::integral_constant"*
  %tmp4 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp5 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* dereferenceable(1) %tmp4) #10
  ret i64 %tmp5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %arg, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %tmp1, i32 0, i32 2
  %tmp3 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %tmp2) #10
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #1 align 2 {
bb:
  %tmp = call i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #10
  ret i64 %tmp
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* dereferenceable(8) %arg, i64* dereferenceable(8) %arg1) #0 {
bb:
  %tmp = alloca %"struct.std::__1::__less", align 1
  %tmp2 = alloca i64*, align 8
  %tmp3 = alloca i64*, align 8
  store i64* %arg, i64** %tmp2, align 8
  store i64* %arg1, i64** %tmp3, align 8
  %tmp4 = load i64*, i64** %tmp3, align 8
  %tmp5 = load i64*, i64** %tmp2, align 8
  %tmp6 = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %tmp, i64* dereferenceable(8) %tmp4, i64* dereferenceable(8) %tmp5)
  br i1 %tmp6, label %bb7, label %bb9

bb7:                                              ; preds = %bb
  %tmp8 = load i64*, i64** %tmp3, align 8
  br label %bb11

bb9:                                              ; preds = %bb
  %tmp10 = load i64*, i64** %tmp2, align 8
  br label %bb11

bb11:                                             ; preds = %bb9, %bb7
  %tmp12 = phi i64* [ %tmp8, %bb7 ], [ %tmp10, %bb9 ]
  ret i64* %tmp12
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %arg, i64* dereferenceable(8) %arg1, i64* dereferenceable(8) %arg2) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__less"*, align 8
  %tmp3 = alloca i64*, align 8
  %tmp4 = alloca i64*, align 8
  store %"struct.std::__1::__less"* %arg, %"struct.std::__1::__less"** %tmp, align 8
  store i64* %arg1, i64** %tmp3, align 8
  store i64* %arg2, i64** %tmp4, align 8
  %tmp5 = load %"struct.std::__1::__less"*, %"struct.std::__1::__less"** %tmp, align 8
  %tmp6 = load i64*, i64** %tmp3, align 8
  %tmp7 = load i64, i64* %tmp6, align 8
  %tmp8 = load i64*, i64** %tmp4, align 8
  %tmp9 = load i64, i64* %tmp8, align 8
  %tmp10 = icmp ult i64 %tmp7, %tmp9
  ret i1 %tmp10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* dereferenceable(1) %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::integral_constant", align 1
  %tmp1 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp1, align 8
  %tmp2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp1, align 8
  %tmp3 = call i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %tmp2) #10
  ret i64 %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  %tmp1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  ret i64 4611686018427387903
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %arg, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair"* %tmp1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %tmp3 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %tmp2) #10
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %arg, %"struct.std::__1::__compressed_pair_elem.0"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %tmp, align 8
  %tmp2 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %tmp1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %tmp2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #1 align 2 {
bb:
  ret i64 9223372036854775807
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* dereferenceable(8) %arg, i64* dereferenceable(8) %arg1) #1 {
bb:
  %tmp = alloca %"struct.std::__1::__less", align 1
  %tmp2 = alloca i64*, align 8
  %tmp3 = alloca i64*, align 8
  store i64* %arg, i64** %tmp2, align 8
  store i64* %arg1, i64** %tmp3, align 8
  %tmp4 = load i64*, i64** %tmp2, align 8
  %tmp5 = load i64*, i64** %tmp3, align 8
  %tmp6 = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %tmp, i64* dereferenceable(8) %tmp4, i64* dereferenceable(8) %tmp5)
  br i1 %tmp6, label %bb7, label %bb9

bb7:                                              ; preds = %bb
  %tmp8 = load i64*, i64** %tmp3, align 8
  br label %bb11

bb9:                                              ; preds = %bb
  %tmp10 = load i64*, i64** %tmp2, align 8
  br label %bb11

bb11:                                             ; preds = %bb9, %bb7
  %tmp12 = phi i64* [ %tmp8, %bb7 ], [ %tmp10, %bb9 ]
  ret i64* %tmp12
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %arg, i64 %arg1, i64 %arg2, %"class.std::__1::allocator"* dereferenceable(1) %arg3) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  %tmp4 = alloca i64, align 8
  %tmp5 = alloca i64, align 8
  %tmp6 = alloca %"class.std::__1::allocator"*, align 8
  %tmp7 = alloca i8*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  store i64 %arg1, i64* %tmp4, align 8
  store i64 %arg2, i64* %tmp5, align 8
  store %"class.std::__1::allocator"* %arg3, %"class.std::__1::allocator"** %tmp6, align 8
  %tmp8 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp9 = bitcast %"struct.std::__1::__split_buffer"* %tmp8 to %"class.std::__1::__split_buffer_common"*
  %tmp10 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 3
  store i8* null, i8** %tmp7, align 8
  %tmp11 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp6, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %tmp10, i8** dereferenceable(8) %tmp7, %"class.std::__1::allocator"* dereferenceable(1) %tmp11)
  %tmp12 = load i64, i64* %tmp4, align 8
  %tmp13 = icmp ne i64 %tmp12, 0
  br i1 %tmp13, label %bb14, label %bb18

bb14:                                             ; preds = %bb
  %tmp15 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %tmp8) #10
  %tmp16 = load i64, i64* %tmp4, align 8
  %tmp17 = call i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* dereferenceable(1) %tmp15, i64 %tmp16)
  br label %bb19

bb18:                                             ; preds = %bb
  br label %bb19

bb19:                                             ; preds = %bb18, %bb14
  %tmp20 = phi i32* [ %tmp17, %bb14 ], [ null, %bb18 ]
  %tmp21 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 0
  store i32* %tmp20, i32** %tmp21, align 8
  %tmp22 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 0
  %tmp23 = load i32*, i32** %tmp22, align 8
  %tmp24 = load i64, i64* %tmp5, align 8
  %tmp25 = getelementptr inbounds i32, i32* %tmp23, i64 %tmp24
  %tmp26 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 2
  store i32* %tmp25, i32** %tmp26, align 8
  %tmp27 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 1
  store i32* %tmp25, i32** %tmp27, align 8
  %tmp28 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp8, i32 0, i32 0
  %tmp29 = load i32*, i32** %tmp28, align 8
  %tmp30 = load i64, i64* %tmp4, align 8
  %tmp31 = getelementptr inbounds i32, i32* %tmp29, i64 %tmp30
  %tmp32 = call dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %tmp8) #10
  store i32* %tmp31, i32** %tmp32, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %arg, i8** dereferenceable(8) %arg1, %"class.std::__1::allocator"* dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  %tmp3 = alloca i8**, align 8
  %tmp4 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  store i8** %arg1, i8*** %tmp3, align 8
  store %"class.std::__1::allocator"* %arg2, %"class.std::__1::allocator"** %tmp4, align 8
  %tmp5 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp6 = load i8**, i8*** %tmp3, align 8
  %tmp7 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp4, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %tmp5, i8** dereferenceable(8) %tmp6, %"class.std::__1::allocator"* dereferenceable(1) %tmp7)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* dereferenceable(1) %arg, i64 %arg1) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp2 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i64 %arg1, i64* %tmp2, align 8
  %tmp3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp4 = load i64, i64* %tmp2, align 8
  %tmp5 = call i32* @_ZNSt3__19allocatorIiE8allocateEmPKv(%"class.std::__1::allocator"* %tmp3, i64 %tmp4, i8* null)
  ret i32* %tmp5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 3
  %tmp3 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.1"* %tmp2) #10
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 3
  %tmp3 = call dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.1"* %arg, i8** dereferenceable(8) %arg1, %"class.std::__1::allocator"* dereferenceable(1) %arg2) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  %tmp3 = alloca i8**, align 8
  %tmp4 = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  store i8** %arg1, i8*** %tmp3, align 8
  store %"class.std::__1::allocator"* %arg2, %"class.std::__1::allocator"** %tmp4, align 8
  %tmp5 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp6 = bitcast %"class.std::__1::__compressed_pair.1"* %tmp5 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp7 = load i8**, i8*** %tmp3, align 8
  %tmp8 = call dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** dereferenceable(8) %tmp7) #10
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %tmp6, i8** dereferenceable(8) %tmp8)
  %tmp9 = bitcast %"class.std::__1::__compressed_pair.1"* %tmp5 to i8*
  %tmp10 = getelementptr inbounds i8, i8* %tmp9, i64 8
  %tmp11 = bitcast i8* %tmp10 to %"struct.std::__1::__compressed_pair_elem.2"*
  %tmp12 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp4, align 8
  %tmp13 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* dereferenceable(1) %tmp12) #10
  call void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %tmp11, %"class.std::__1::allocator"* dereferenceable(1) %tmp13)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* dereferenceable(1) %arg) #1 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  %tmp1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  ret %"class.std::__1::allocator"* %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %arg, %"class.std::__1::allocator"* dereferenceable(1) %arg1) unnamed_addr #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  %tmp2 = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %arg, %"struct.std::__1::__compressed_pair_elem.2"** %tmp, align 8
  store %"class.std::__1::allocator"* %arg1, %"class.std::__1::allocator"** %tmp2, align 8
  %tmp3 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %tmp, align 8
  %tmp4 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.2", %"struct.std::__1::__compressed_pair_elem.2"* %tmp3, i32 0, i32 0
  %tmp5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp2, align 8
  %tmp6 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* dereferenceable(1) %tmp5) #10
  store %"class.std::__1::allocator"* %tmp6, %"class.std::__1::allocator"** %tmp4, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__19allocatorIiE8allocateEmPKv(%"class.std::__1::allocator"* %arg, i64 %arg1, i8* %arg2) #0 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp3 = alloca i64, align 8
  %tmp4 = alloca i8*, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i64 %arg1, i64* %tmp3, align 8
  store i8* %arg2, i8** %tmp4, align 8
  %tmp5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp, align 8
  %tmp6 = load i64, i64* %tmp3, align 8
  %tmp7 = call i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %tmp5) #10
  %tmp8 = icmp ugt i64 %tmp6, %tmp7
  br i1 %tmp8, label %bb9, label %bb10

bb9:                                              ; preds = %bb
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str, i64 0, i64 0)) #13
  unreachable

bb10:                                             ; preds = %bb
  %tmp11 = load i64, i64* %tmp3, align 8
  %tmp12 = mul i64 %tmp11, 4
  %tmp13 = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %tmp12, i64 4)
  %tmp14 = bitcast i8* %tmp13 to i32*
  ret i32* %tmp14
}

; Function Attrs: noinline noreturn optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__throw_length_errorEPKc(i8* %arg) #5 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca i8*, align 8
  %tmp1 = alloca i8*
  %tmp2 = alloca i32
  store i8* %arg, i8** %tmp, align 8
  %tmp3 = call i8* @__cxa_allocate_exception(i64 16) #10
  %tmp4 = bitcast i8* %tmp3 to %"class.std::length_error"*
  %tmp5 = load i8*, i8** %tmp, align 8
  call void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %tmp4, i8* %tmp5)
  br label %bb6

bb6:                                              ; preds = %bb
  call void @__cxa_throw(i8* %tmp3, i8* bitcast (i8** @_ZTISt12length_error to i8*), i8* bitcast (void (%"class.std::length_error"*)* @_ZNSt12length_errorD1Ev to i8*)) #13
  unreachable
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %arg, i64 %arg1) #0 {
bb:
  %tmp = alloca i64, align 8
  %tmp2 = alloca i64, align 8
  store i64 %arg, i64* %tmp, align 8
  store i64 %arg1, i64* %tmp2, align 8
  %tmp3 = load i64, i64* %tmp, align 8
  %tmp4 = call i8* @_Znwm(i64 %tmp3) #14
  ret i8* %tmp4
}

declare i8* @__cxa_allocate_exception(i64)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %arg, i8* %arg1) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::length_error"*, align 8
  %tmp2 = alloca i8*, align 8
  store %"class.std::length_error"* %arg, %"class.std::length_error"** %tmp, align 8
  store i8* %arg1, i8** %tmp2, align 8
  %tmp3 = load %"class.std::length_error"*, %"class.std::length_error"** %tmp, align 8
  %tmp4 = load i8*, i8** %tmp2, align 8
  call void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %tmp3, i8* %tmp4)
  ret void
}

declare void @__cxa_free_exception(i8*)

; Function Attrs: nounwind
declare void @_ZNSt12length_errorD1Ev(%"class.std::length_error"*) unnamed_addr #6

declare void @__cxa_throw(i8*, i8*, i8*)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %arg, i8* %arg1) unnamed_addr #0 align 2 {
bb:
  %tmp = alloca %"class.std::length_error"*, align 8
  %tmp2 = alloca i8*, align 8
  store %"class.std::length_error"* %arg, %"class.std::length_error"** %tmp, align 8
  store i8* %arg1, i8** %tmp2, align 8
  %tmp3 = load %"class.std::length_error"*, %"class.std::length_error"** %tmp, align 8
  %tmp4 = bitcast %"class.std::length_error"* %tmp3 to %"class.std::logic_error"*
  %tmp5 = load i8*, i8** %tmp2, align 8
  call void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"* %tmp4, i8* %tmp5)
  %tmp6 = bitcast %"class.std::length_error"* %tmp3 to i32 (...)***
  store i32 (...)** bitcast (i8** getelementptr inbounds ({ [5 x i8*] }, { [5 x i8*] }* @_ZTVSt12length_error, i32 0, inrange i32 0, i32 2) to i32 (...)**), i32 (...)*** %tmp6, align 8
  ret void
}

declare void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"*, i8*) unnamed_addr #7

; Function Attrs: nobuiltin
declare noalias i8* @_Znwm(i64) #8

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.1"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair.1"* %tmp1 to i8*
  %tmp3 = getelementptr inbounds i8, i8* %tmp2, i64 8
  %tmp4 = bitcast i8* %tmp3 to %"struct.std::__1::__compressed_pair_elem.2"*
  %tmp5 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %tmp4) #10
  ret %"class.std::__1::allocator"* %tmp5
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %arg, %"struct.std::__1::__compressed_pair_elem.2"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.2", %"struct.std::__1::__compressed_pair_elem.2"* %tmp1, i32 0, i32 0
  %tmp3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %tmp2, align 8
  ret %"class.std::__1::allocator"* %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair.1"* %tmp1 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp3 = call dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* dereferenceable(1) %arg, i32* %arg1, i32* %arg2, i32** dereferenceable(8) %arg3) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::allocator"*, align 8
  %tmp4 = alloca i32*, align 8
  %tmp5 = alloca i32*, align 8
  %tmp6 = alloca i32**, align 8
  %tmp7 = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %tmp, align 8
  store i32* %arg1, i32** %tmp4, align 8
  store i32* %arg2, i32** %tmp5, align 8
  store i32** %arg3, i32*** %tmp6, align 8
  %tmp8 = load i32*, i32** %tmp5, align 8
  %tmp9 = load i32*, i32** %tmp4, align 8
  %tmp10 = ptrtoint i32* %tmp8 to i64
  %tmp11 = ptrtoint i32* %tmp9 to i64
  %tmp12 = sub i64 %tmp10, %tmp11
  %tmp13 = sdiv exact i64 %tmp12, 4
  store i64 %tmp13, i64* %tmp7, align 8
  %tmp14 = load i64, i64* %tmp7, align 8
  %tmp15 = load i32**, i32*** %tmp6, align 8
  %tmp16 = load i32*, i32** %tmp15, align 8
  %tmp17 = sub i64 0, %tmp14
  %tmp18 = getelementptr inbounds i32, i32* %tmp16, i64 %tmp17
  store i32* %tmp18, i32** %tmp15, align 8
  %tmp19 = load i64, i64* %tmp7, align 8
  %tmp20 = icmp sgt i64 %tmp19, 0
  br i1 %tmp20, label %bb21, label %bb29

bb21:                                             ; preds = %bb
  %tmp22 = load i32**, i32*** %tmp6, align 8
  %tmp23 = load i32*, i32** %tmp22, align 8
  %tmp24 = bitcast i32* %tmp23 to i8*
  %tmp25 = load i32*, i32** %tmp4, align 8
  %tmp26 = bitcast i32* %tmp25 to i8*
  %tmp27 = load i64, i64* %tmp7, align 8
  %tmp28 = mul i64 %tmp27, 4
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %tmp24, i8* align 4 %tmp26, i64 %tmp28, i1 false)
  br label %bb29

bb29:                                             ; preds = %bb21, %bb
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** dereferenceable(8) %arg, i32** dereferenceable(8) %arg1) #1 {
bb:
  %tmp = alloca i32**, align 8
  %tmp2 = alloca i32**, align 8
  %tmp3 = alloca i32*, align 8
  store i32** %arg, i32*** %tmp, align 8
  store i32** %arg1, i32*** %tmp2, align 8
  %tmp4 = load i32**, i32*** %tmp, align 8
  %tmp5 = call dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** dereferenceable(8) %tmp4) #10
  %tmp6 = load i32*, i32** %tmp5, align 8
  store i32* %tmp6, i32** %tmp3, align 8
  %tmp7 = load i32**, i32*** %tmp2, align 8
  %tmp8 = call dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** dereferenceable(8) %tmp7) #10
  %tmp9 = load i32*, i32** %tmp8, align 8
  %tmp10 = load i32**, i32*** %tmp, align 8
  store i32* %tmp9, i32** %tmp10, align 8
  %tmp11 = call dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** dereferenceable(8) %tmp3) #10
  %tmp12 = load i32*, i32** %tmp11, align 8
  %tmp13 = load i32**, i32*** %tmp2, align 8
  store i32* %tmp12, i32** %tmp13, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %arg, i64 %arg1) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  %tmp2 = alloca i64, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  store i64 %arg1, i64* %tmp2, align 8
  %tmp3 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  %tmp4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp5 = bitcast i32* %tmp4 to i8*
  %tmp6 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp7 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp8 = getelementptr inbounds i32, i32* %tmp6, i64 %tmp7
  %tmp9 = bitcast i32* %tmp8 to i8*
  %tmp10 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp11 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp12 = getelementptr inbounds i32, i32* %tmp10, i64 %tmp11
  %tmp13 = bitcast i32* %tmp12 to i8*
  %tmp14 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %tmp3) #10
  %tmp15 = load i64, i64* %tmp2, align 8
  %tmp16 = getelementptr inbounds i32, i32* %tmp14, i64 %tmp15
  %tmp17 = bitcast i32* %tmp16 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %tmp3, i8* %tmp5, i8* %tmp9, i8* %tmp13, i8* %tmp17) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %arg, %"class.std::__1::vector"** %tmp, align 8
  %tmp1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %tmp, align 8
  ret void
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #9

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** dereferenceable(8) %arg) #1 {
bb:
  %tmp = alloca i32**, align 8
  store i32** %arg, i32*** %tmp, align 8
  %tmp1 = load i32**, i32*** %tmp, align 8
  ret i32** %tmp1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %arg) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %tmp1) #10
  %tmp2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 0
  %tmp3 = load i32*, i32** %tmp2, align 8
  %tmp4 = icmp ne i32* %tmp3, null
  br i1 %tmp4, label %bb5, label %bb11

bb5:                                              ; preds = %bb
  %tmp6 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %tmp1) #10
  %tmp7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 0
  %tmp8 = load i32*, i32** %tmp7, align 8
  %tmp9 = call i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %tmp1)
  br label %bb10

bb10:                                             ; preds = %bb5
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* dereferenceable(1) %tmp6, i32* %tmp8, i64 %tmp9) #10
  br label %bb11

bb11:                                             ; preds = %bb10, %bb
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 1
  %tmp3 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %tmp1, i32* %tmp3) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp2 = call dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %tmp1) #10
  %tmp3 = load i32*, i32** %tmp2, align 8
  %tmp4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 0
  %tmp5 = load i32*, i32** %tmp4, align 8
  %tmp6 = ptrtoint i32* %tmp3 to i64
  %tmp7 = ptrtoint i32* %tmp5 to i64
  %tmp8 = sub i64 %tmp6, %tmp7
  %tmp9 = sdiv exact i64 %tmp8, 4
  ret i64 %tmp9
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %arg, i32* %arg1) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  %tmp2 = alloca i32*, align 8
  %tmp3 = alloca %"struct.std::__1::integral_constant.3", align 1
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  store i32* %arg1, i32** %tmp2, align 8
  %tmp4 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp5 = load i32*, i32** %tmp2, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %tmp4, i32* %tmp5) #10
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %arg, i32* %arg1) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
bb:
  %tmp = alloca %"struct.std::__1::integral_constant.3", align 1
  %tmp2 = alloca %"struct.std::__1::__split_buffer"*, align 8
  %tmp3 = alloca i32*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  store i32* %arg1, i32** %tmp3, align 8
  %tmp4 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp2, align 8
  br label %bb5

bb5:                                              ; preds = %bb16, %bb
  %tmp6 = load i32*, i32** %tmp3, align 8
  %tmp7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp4, i32 0, i32 2
  %tmp8 = load i32*, i32** %tmp7, align 8
  %tmp9 = icmp ne i32* %tmp6, %tmp8
  br i1 %tmp9, label %bb10, label %bb17

bb10:                                             ; preds = %bb5
  %tmp11 = call dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %tmp4) #10
  %tmp12 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp4, i32 0, i32 2
  %tmp13 = load i32*, i32** %tmp12, align 8
  %tmp14 = getelementptr inbounds i32, i32* %tmp13, i32 -1
  store i32* %tmp14, i32** %tmp12, align 8
  %tmp15 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %tmp14) #10
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* dereferenceable(1) %tmp11, i32* %tmp15)
  br label %bb16

bb16:                                             ; preds = %bb10
  br label %bb5

bb17:                                             ; preds = %bb5
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %arg, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %tmp, align 8
  %tmp2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %tmp1, i32 0, i32 3
  %tmp3 = call dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %tmp2) #10
  ret i32** %tmp3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.1"* %arg) #1 align 2 {
bb:
  %tmp = alloca %"class.std::__1::__compressed_pair.1"*, align 8
  store %"class.std::__1::__compressed_pair.1"* %arg, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp1 = load %"class.std::__1::__compressed_pair.1"*, %"class.std::__1::__compressed_pair.1"** %tmp, align 8
  %tmp2 = bitcast %"class.std::__1::__compressed_pair.1"* %tmp1 to %"struct.std::__1::__compressed_pair_elem"*
  %tmp3 = call dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %tmp2) #10
  ret i32** %tmp3
}

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline noreturn nounwind }
attributes #3 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noinline noreturn optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { nobuiltin "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { argmemonly nounwind willreturn }
attributes #10 = { nounwind }
attributes #11 = { noreturn nounwind }
attributes #12 = { builtin nounwind }
attributes #13 = { noreturn }
attributes #14 = { builtin }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.0 "}
