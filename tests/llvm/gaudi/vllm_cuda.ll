; ModuleID = 'gaudi/vllm_cuda.ll'
source_filename = "gaudi/vllm_cuda.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }
%"class.std::__1::tuple" = type { %"struct.std::__1::__tuple_impl" }
%"struct.std::__1::__tuple_impl" = type { %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf.1" }
%"class.std::__1::__tuple_leaf" = type { i32 }
%"class.std::__1::__tuple_leaf.1" = type { i32 }
%"struct.std::__1::__tuple_indices" = type { i8 }
%"struct.std::__1::__tuple_types" = type { i8 }
%"struct.std::__1::__tuple_indices.2" = type { i8 }
%"struct.std::__1::__tuple_types.3" = type { i8 }
%"struct.std::__1::__default_init_tag" = type { i8 }
%"class.std::__1::__vector_base_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.0" = type { i8 }
%"class.std::__1::allocator" = type { i8 }
%"struct.std::__1::integral_constant" = type { i8 }
%"struct.std::__1::__has_destroy" = type { i8 }
%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction" = type { %"class.std::__1::vector"*, i32*, i32* }
%"struct.std::__1::__split_buffer" = type { i32*, i32*, i32*, %"class.std::__1::__compressed_pair.4" }
%"class.std::__1::__compressed_pair.4" = type { %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem.5" }
%"struct.std::__1::__compressed_pair_elem.5" = type { %"class.std::__1::allocator"* }
%"struct.std::__1::__has_construct" = type { i8 }
%"struct.std::__1::__less" = type { i8 }
%"struct.std::__1::__has_max_size" = type { i8 }
%"class.std::__1::__split_buffer_common" = type { i8 }
%"class.std::length_error" = type { %"class.std::logic_error" }
%"class.std::logic_error" = type { %"class.std::exception", %"class.std::__1::__libcpp_refstring" }
%"class.std::exception" = type { i32 (...)** }
%"class.std::__1::__libcpp_refstring" = type { i8* }
%"struct.std::__1::integral_constant.6" = type { i8 }

@.str = private unnamed_addr constant [68 x i8] c"allocator<T>::allocate(size_t n) 'n' exceeds maximum supported size\00", align 1
@_ZTISt12length_error = external constant i8*
@_ZTVSt12length_error = external unnamed_addr constant { [5 x i8*] }, align 8

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @_Z4silui(i32 %x) #0 {
entry:
  %x.addr = alloca i32, align 4
  store i32 %x, i32* %x.addr, align 4
  %i = load i32, i32* %x.addr, align 4
  %conv = sitofp i32 %i to double
  %i1 = load i32, i32* %x.addr, align 4
  %sub = sub nsw i32 0, %i1
  %call = call double @_Z3expIiENSt3__19enable_ifIXsr3std11is_integralIT_EE5valueEdE4typeES2_(i32 %sub) #12
  %add = fadd double 1.000000e+00, %call
  %div = fdiv double %conv, %add
  %conv1 = fptosi double %div to i32
  ret i32 %conv1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden double @_Z3expIiENSt3__19enable_ifIXsr3std11is_integralIT_EE5valueEdE4typeES2_(i32 %__lcpp_x) #0 {
entry:
  %__lcpp_x.addr = alloca i32, align 4
  store i32 %__lcpp_x, i32* %__lcpp_x.addr, align 4
  %i = load i32, i32* %__lcpp_x.addr, align 4
  %conv = sitofp i32 %i to double
  %i1 = call double @llvm.exp.f64(double %conv)
  ret double %i1
}

; Function Attrs: noinline optnone ssp uwtable
define void @_Z18activation_kernelsNSt3__16vectorIiNS_9allocatorIiEEEES3_(%"class.std::__1::vector"* noalias sret align 8 %agg.result, %"class.std::__1::vector"* %x, %"class.std::__1::vector"* %y) #1 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %result.ptr = alloca i8*, align 8
  %nrvo = alloca i1, align 1
  %i = alloca i32, align 4
  %ref.tmp = alloca i32, align 4
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  %i1 = bitcast %"class.std::__1::vector"* %agg.result to i8*
  store i8* %i1, i8** %result.ptr, align 8
  store i1 false, i1* %nrvo, align 1
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %agg.result) #12
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i2 = load i32, i32* %i, align 4
  %conv = sext i32 %i2 to i64
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %x) #12
  %cmp = icmp ult i64 %conv, %call
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %i3 = load i32, i32* %i, align 4
  %conv1 = sext i32 %i3 to i64
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %x, i64 %conv1) #12
  %i4 = load i32, i32* %call2, align 4
  %call3 = call i32 @_Z4silui(i32 %i4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %for.body
  %i5 = load i32, i32* %i, align 4
  %conv4 = sext i32 %i5 to i64
  %call5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %y, i64 %conv4) #12
  %i6 = load i32, i32* %call5, align 4
  %mul = mul nsw i32 %call3, %i6
  store i32 %mul, i32* %ref.tmp, align 4
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backEOi(%"class.std::__1::vector"* %agg.result, i32* nonnull align 4 dereferenceable(4) %ref.tmp)
  br label %invoke.cont6

invoke.cont6:                                     ; preds = %invoke.cont
  br label %for.inc

for.inc:                                          ; preds = %invoke.cont6
  %i7 = load i32, i32* %i, align 4
  %inc = add nsw i32 %i7, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  store i1 true, i1* %nrvo, align 1
  %nrvo.val = load i1, i1* %nrvo, align 1
  br i1 %nrvo.val, label %nrvo.skipdtor, label %nrvo.unused

nrvo.unused:                                      ; preds = %for.end
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector"* %agg.result) #12
  br label %nrvo.skipdtor

nrvo.skipdtor:                                    ; preds = %nrvo.unused, %for.end
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %this1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i3 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backEOi(%"class.std::__1::vector"* %this, i32* nonnull align 4 dereferenceable(4) %__x) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca i32*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i32* %__x, i32** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i2) #12
  %i3 = load i32*, i32** %call, align 8
  %cmp = icmp ult i32* %i1, %i3
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i4 = load i32*, i32** %__x.addr, align 8
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %i4) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJiEEEvDpOT_(%"class.std::__1::vector"* %this1, i32* nonnull align 4 dereferenceable(4) %call2)
  br label %if.end

if.else:                                          ; preds = %entry
  %i5 = load i32*, i32** %__x.addr, align 8
  %call3 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %i5) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIiEEvOT_(%"class.std::__1::vector"* %this1, i32* nonnull align 4 dereferenceable(4) %call3)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %i2
  ret i32* %arrayidx
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector"* %this1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @_Z19layernorm_kernels_1NSt3__16vectorIiNS_9allocatorIiEEEES3_ii(%"class.std::__1::vector"* %input, %"class.std::__1::vector"* %weight, i32 %epsilon, i32 %hidden_size) #0 {
entry:
  %epsilon.addr = alloca i32, align 4
  %hidden_size.addr = alloca i32, align 4
  %variance = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 %epsilon, i32* %epsilon.addr, align 4
  store i32 %hidden_size, i32* %hidden_size.addr, align 4
  store i32 0, i32* %variance, align 4
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i1 = load i32, i32* %i, align 4
  %conv = sext i32 %i1 to i64
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %input) #12
  %cmp = icmp ult i64 %conv, %call
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %i2 = load i32, i32* %i, align 4
  %conv1 = sext i32 %i2 to i64
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv1) #12
  %i3 = load i32, i32* %call2, align 4
  %i4 = load i32, i32* %i, align 4
  %conv3 = sext i32 %i4 to i64
  %call4 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv3) #12
  %i5 = load i32, i32* %call4, align 4
  %mul = mul nsw i32 %i3, %i5
  %i6 = load i32, i32* %variance, align 4
  %add = add nsw i32 %i6, %mul
  store i32 %add, i32* %variance, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %i7 = load i32, i32* %i, align 4
  %inc = add nsw i32 %i7, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %i8 = load i32, i32* %variance, align 4
  ret i32 %i8
}

; Function Attrs: noinline optnone ssp uwtable
define void @_Z19layernorm_kernels_2NSt3__16vectorIiNS_9allocatorIiEEEES3_iii(%"class.std::__1::vector"* noalias sret align 8 %agg.result, %"class.std::__1::vector"* %input, %"class.std::__1::vector"* %weight, i32 %epsilon, i32 %hidden_size, i32 %variance) #1 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %result.ptr = alloca i8*, align 8
  %epsilon.addr = alloca i32, align 4
  %hidden_size.addr = alloca i32, align 4
  %variance.addr = alloca i32, align 4
  %s_variance = alloca i32, align 4
  %nrvo = alloca i1, align 1
  %i = alloca i32, align 4
  %ref.tmp = alloca i32, align 4
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  %i1 = bitcast %"class.std::__1::vector"* %agg.result to i8*
  store i8* %i1, i8** %result.ptr, align 8
  store i32 %epsilon, i32* %epsilon.addr, align 4
  store i32 %hidden_size, i32* %hidden_size.addr, align 4
  store i32 %variance, i32* %variance.addr, align 4
  %i2 = load i32, i32* %variance.addr, align 4
  %i3 = load i32, i32* %epsilon.addr, align 4
  %add = add nsw i32 %i2, %i3
  store i32 %add, i32* %s_variance, align 4
  store i1 false, i1* %nrvo, align 1
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %agg.result) #12
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i4 = load i32, i32* %i, align 4
  %conv = sext i32 %i4 to i64
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %input) #12
  %cmp = icmp ult i64 %conv, %call
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %i5 = load i32, i32* %i, align 4
  %conv1 = sext i32 %i5 to i64
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv1) #12
  %i6 = load i32, i32* %call2, align 4
  %i7 = load i32, i32* %s_variance, align 4
  %mul = mul nsw i32 %i6, %i7
  %i8 = load i32, i32* %i, align 4
  %conv3 = sext i32 %i8 to i64
  %call4 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %weight, i64 %conv3) #12
  %i9 = load i32, i32* %call4, align 4
  %mul5 = mul nsw i32 %mul, %i9
  store i32 %mul5, i32* %ref.tmp, align 4
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backEOi(%"class.std::__1::vector"* %agg.result, i32* nonnull align 4 dereferenceable(4) %ref.tmp)
  br label %invoke.cont

invoke.cont:                                      ; preds = %for.body
  br label %for.inc

for.inc:                                          ; preds = %invoke.cont
  %i10 = load i32, i32* %i, align 4
  %inc = add nsw i32 %i10, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  store i1 true, i1* %nrvo, align 1
  %nrvo.val = load i1, i1* %nrvo, align 1
  br i1 %nrvo.val, label %nrvo.skipdtor, label %nrvo.unused

nrvo.unused:                                      ; preds = %for.end
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector"* %agg.result) #12
  br label %nrvo.skipdtor

nrvo.skipdtor:                                    ; preds = %nrvo.unused, %for.end
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i64 @_Z20get_rotary_embeddingNSt3__16vectorIiNS_9allocatorIiEEEES3_S3_iib(%"class.std::__1::vector"* %input, %"class.std::__1::vector"* %cos_cache, %"class.std::__1::vector"* %sin_cache, i32 %rot_offset, i32 %embed_dim, i1 zeroext %is_neox) #0 {
entry:
  %retval = alloca %"class.std::__1::tuple", align 4
  %rot_offset.addr = alloca i32, align 4
  %embed_dim.addr = alloca i32, align 4
  %is_neox.addr = alloca i8, align 1
  %x_index = alloca i32, align 4
  %y_index = alloca i32, align 4
  %cos = alloca i32, align 4
  %sin = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %ref.tmp = alloca i32, align 4
  %ref.tmp16 = alloca i32, align 4
  store i32 %rot_offset, i32* %rot_offset.addr, align 4
  store i32 %embed_dim, i32* %embed_dim.addr, align 4
  %frombool = zext i1 %is_neox to i8
  store i8 %frombool, i8* %is_neox.addr, align 1
  %i = load i8, i8* %is_neox.addr, align 1
  %tobool = trunc i8 %i to i1
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i1 = load i32, i32* %rot_offset.addr, align 4
  store i32 %i1, i32* %x_index, align 4
  %i2 = load i32, i32* %embed_dim.addr, align 4
  %i3 = load i32, i32* %rot_offset.addr, align 4
  %add = add nsw i32 %i2, %i3
  store i32 %add, i32* %y_index, align 4
  %i4 = load i32, i32* %x_index, align 4
  %conv = sext i32 %i4 to i64
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %cos_cache, i64 %conv) #12
  %i5 = load i32, i32* %call, align 4
  store i32 %i5, i32* %cos, align 4
  %i6 = load i32, i32* %x_index, align 4
  %conv1 = sext i32 %i6 to i64
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %sin_cache, i64 %conv1) #12
  %i7 = load i32, i32* %call2, align 4
  store i32 %i7, i32* %sin, align 4
  br label %if.end

if.else:                                          ; preds = %entry
  %i8 = load i32, i32* %rot_offset.addr, align 4
  %mul = mul nsw i32 2, %i8
  store i32 %mul, i32* %x_index, align 4
  %i9 = load i32, i32* %rot_offset.addr, align 4
  %mul3 = mul nsw i32 2, %i9
  %add4 = add nsw i32 %mul3, 1
  store i32 %add4, i32* %y_index, align 4
  %i10 = load i32, i32* %x_index, align 4
  %div = sdiv i32 %i10, 2
  %conv5 = sext i32 %div to i64
  %call6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %cos_cache, i64 %conv5) #12
  %i11 = load i32, i32* %call6, align 4
  store i32 %i11, i32* %cos, align 4
  %i12 = load i32, i32* %x_index, align 4
  %div7 = sdiv i32 %i12, 2
  %conv8 = sext i32 %div7 to i64
  %call9 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %sin_cache, i64 %conv8) #12
  %i13 = load i32, i32* %call9, align 4
  store i32 %i13, i32* %sin, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %i14 = load i32, i32* %x_index, align 4
  %conv10 = sext i32 %i14 to i64
  %call11 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv10) #12
  %i15 = load i32, i32* %call11, align 4
  store i32 %i15, i32* %x, align 4
  %i16 = load i32, i32* %y_index, align 4
  %conv12 = sext i32 %i16 to i64
  %call13 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv12) #12
  %i17 = load i32, i32* %call13, align 4
  store i32 %i17, i32* %y, align 4
  %i18 = load i32, i32* %x, align 4
  %i19 = load i32, i32* %cos, align 4
  %mul14 = mul nsw i32 %i18, %i19
  %i20 = load i32, i32* %y, align 4
  %i21 = load i32, i32* %sin, align 4
  %mul15 = mul nsw i32 %i20, %i21
  %sub = sub nsw i32 %mul14, %mul15
  store i32 %sub, i32* %ref.tmp, align 4
  %i22 = load i32, i32* %y, align 4
  %i23 = load i32, i32* %cos, align 4
  %mul17 = mul nsw i32 %i22, %i23
  %i24 = load i32, i32* %x, align 4
  %i25 = load i32, i32* %sin, align 4
  %mul18 = mul nsw i32 %i24, %i25
  %add19 = add nsw i32 %mul17, %mul18
  store i32 %add19, i32* %ref.tmp16, align 4
  call void @_ZNSt3__15tupleIJiiEEC1IJiiELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %retval, i32* nonnull align 4 dereferenceable(4) %ref.tmp, i32* nonnull align 4 dereferenceable(4) %ref.tmp16) #12
  %coerce.dive = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %retval, i32 0, i32 0
  %i26 = bitcast %"struct.std::__1::__tuple_impl"* %coerce.dive to i64*
  %i27 = load i64, i64* %i26, align 4
  ret i64 %i27
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC1IJiiELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u1) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr2 = alloca i32*, align 8
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u1, i32** %__u.addr2, align 8
  %this3 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %i = load i32*, i32** %__u.addr, align 8
  %i1 = load i32*, i32** %__u.addr2, align 8
  call void @_ZNSt3__15tupleIJiiEEC2IJiiELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %this3, i32* nonnull align 4 dereferenceable(4) %i, i32* nonnull align 4 dereferenceable(4) %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @_Z16rotary_embeddingNSt3__16vectorIiNS_9allocatorIiEEEE(%"class.std::__1::vector"* noalias sret align 8 %agg.result, %"class.std::__1::vector"* %input) #0 {
entry:
  %result.ptr = alloca i8*, align 8
  %i = bitcast %"class.std::__1::vector"* %agg.result to i8*
  store i8* %i, i8** %result.ptr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector"* %agg.result) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC2IJiiELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u1) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr2 = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::__tuple_indices", align 1
  %agg.tmp4 = alloca %"struct.std::__1::__tuple_types", align 1
  %agg.tmp5 = alloca %"struct.std::__1::__tuple_indices.2", align 1
  %agg.tmp6 = alloca %"struct.std::__1::__tuple_types.3", align 1
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u1, i32** %__u.addr2, align 8
  %this3 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %__base_ = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %this3, i32 0, i32 0
  %i = load i32*, i32** %__u.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #12
  %i1 = load i32*, i32** %__u.addr2, align 8
  %call7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i1) #12
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJiiEEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS6_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %__base_, i32* nonnull align 4 dereferenceable(4) %call, i32* nonnull align 4 dereferenceable(4) %call7) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %__t) #0 {
entry:
  %__t.addr = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJiiEEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS6_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u4) unnamed_addr #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i1 = alloca %"struct.std::__1::__tuple_types", align 1
  %i2 = alloca %"struct.std::__1::__tuple_indices.2", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types.3", align 1
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr5 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u4, i32** %__u.addr5, align 8
  %this6 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i4 = load i32*, i32** %__u.addr, align 8
  %i5 = load i32*, i32** %__u.addr5, align 8
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJiiEEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS6_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %this6, i32* nonnull align 4 dereferenceable(4) %i4, i32* nonnull align 4 dereferenceable(4) %i5) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJiiEEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS6_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u4) unnamed_addr #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i1 = alloca %"struct.std::__1::__tuple_types", align 1
  %i2 = alloca %"struct.std::__1::__tuple_indices.2", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types.3", align 1
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr5 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u4, i32** %__u.addr5, align 8
  %this6 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i4 = bitcast %"struct.std::__1::__tuple_impl"* %this6 to %"class.std::__1::__tuple_leaf"*
  %i5 = load i32*, i32** %__u.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i5) #12
  call void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IivEEOT_(%"class.std::__1::__tuple_leaf"* %i4, i32* nonnull align 4 dereferenceable(4) %call) #12
  %i6 = bitcast %"struct.std::__1::__tuple_impl"* %this6 to i8*
  %i7 = getelementptr inbounds i8, i8* %i6, i64 4
  %i8 = bitcast i8* %i7 to %"class.std::__1::__tuple_leaf.1"*
  %i9 = load i32*, i32** %__u.addr5, align 8
  %call7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i9) #12
  call void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IivEEOT_(%"class.std::__1::__tuple_leaf.1"* %i8, i32* nonnull align 4 dereferenceable(4) %call7) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IivEEOT_(%"class.std::__1::__tuple_leaf"* %this, i32* nonnull align 4 dereferenceable(4) %__t) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf"* %this, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #12
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %__value_, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IivEEOT_(%"class.std::__1::__tuple_leaf.1"* %this, i32* nonnull align 4 dereferenceable(4) %__t) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf.1"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf.1"* %this, %"class.std::__1::__tuple_leaf.1"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf.1"*, %"class.std::__1::__tuple_leaf.1"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf.1", %"class.std::__1::__tuple_leaf.1"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #12
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %__value_, align 4
  ret void
}

; Function Attrs: nounwind readnone speculatable willreturn
declare double @llvm.exp.f64(double) #2

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %i) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base"* %this) unnamed_addr #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  %ref.tmp = alloca i8*, align 8
  %ref.tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__vector_base"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  store i32* null, i32** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  store i32* null, i32** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base_common"*, align 8
  store %"class.std::__1::__vector_base_common"* %this, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base_common"*, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline noreturn nounwind
define linkonce_odr hidden void @__clang_call_terminate(i8* %arg) #3 {
bb:
  %i = call i8* @__cxa_begin_catch(i8* %arg) #12
  call void @_ZSt9terminatev() #13
  unreachable
}

declare i8* @__cxa_begin_catch(i8*)

declare void @_ZSt9terminatev()

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %agg.tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #12
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #12
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %__t) #0 {
entry:
  %__t.addr = alloca i8**, align 8
  store i8** %__t, i8*** %__t.addr, align 8
  %i = load i8**, i8*** %__t.addr, align 8
  ret i8** %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %this, i8** nonnull align 8 dereferenceable(8) %__u) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  %__u.addr = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  store i8** %__u, i8*** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  %i = load i8**, i8*** %__u.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i) #12
  store i32* null, i32** %__value_, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t) #0 {
entry:
  %__t.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"struct.std::__1::__default_init_tag"* %__t, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  %i = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  ret %"struct.std::__1::__default_init_tag"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %this) unnamed_addr #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  call void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %i1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %this1) #12
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base"* %i) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %i = bitcast i32* %call to i8*
  %call2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this1) #12
  %add.ptr = getelementptr inbounds i32, i32* %call2, i64 %call3
  %i1 = bitcast i32* %add.ptr to i8*
  %call4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %call5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this1) #12
  %add.ptr6 = getelementptr inbounds i32, i32* %call4, i64 %call5
  %i2 = bitcast i32* %add.ptr6 to i8*
  %call7 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %call8 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this1) #12
  %add.ptr9 = getelementptr inbounds i32, i32* %call7, i64 %call8
  %i3 = bitcast i32* %add.ptr9 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i3) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__begin_, align 8
  %cmp = icmp ne i32* %i, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base"* %this1) #12
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %this1) #12
  %__begin_2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_2, align 8
  %call3 = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %this1) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i1, i64 %call3) #12
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %this, i8* %arg, i8* %arg1, i8* %arg2, i8* %arg3) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %.addr = alloca i8*, align 8
  %.addr1 = alloca i8*, align 8
  %.addr2 = alloca i8*, align 8
  %.addr3 = alloca i8*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i8* %arg, i8** %.addr, align 8
  store i8* %arg1, i8** %.addr1, align 8
  store i8* %arg2, i8** %.addr2, align 8
  store i8* %arg3, i8** %.addr3, align 8
  %this4 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %call = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i1) #12
  ret i32* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %i) #12
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %__p) #0 {
entry:
  %__p.addr = alloca i32*, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %i = load i32*, i32** %__p.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %this1) #12
  %i = load i32*, i32** %call, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #12
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #12
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret i32** %__value_
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__begin_, align 8
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base"* %this1, i32* %i) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i64 %__n) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load i32*, i32** %__p.addr, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %i, i32* %i1, i64 %i2) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base"* %this, i32* %__new_last) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  %__new_last.addr = alloca i32*, align 8
  %__soon_to_be_end = alloca i32*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  store i32* %__new_last, i32** %__new_last.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__end_, align 8
  store i32* %i, i32** %__soon_to_be_end, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load i32*, i32** %__new_last.addr, align 8
  %i2 = load i32*, i32** %__soon_to_be_end, align 8
  %cmp = icmp ne i32* %i1, %i2
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %this1) #12
  %i3 = load i32*, i32** %__soon_to_be_end, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 -1
  store i32* %incdec.ptr, i32** %__soon_to_be_end, align 8
  %call2 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %incdec.ptr) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call2)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %i4 = load i32*, i32** %__new_last.addr, align 8
  %__end_3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  store i32* %i4, i32** %__end_3, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_destroy", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %i = bitcast %"struct.std::__1::__has_destroy"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load i32*, i32** %__p.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, i32* %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load i32*, i32** %__p.addr, align 8
  call void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %i1, i32* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %this, i32* %__p) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %this, i32* %__p, i64 %__n) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load i32*, i32** %__p.addr, align 8
  %i1 = bitcast i32* %i to i8*
  %i2 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i2, 4
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %i1, i64 %mul, i64 4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %__ptr, i64 %__size, i64 %__align) #1 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  %i1 = load i64, i64* %__size.addr, align 8
  %i2 = load i64, i64* %__align.addr, align 8
  call void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %i, i64 %i1, i64 %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %__ptr, i64 %__size, i64 %__align) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  %__align_val = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #12
  br i1 %call, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i1 = load i64, i64* %__align.addr, align 8
  store i64 %i1, i64* %__align_val, align 8
  %i2 = load i8*, i8** %__ptr.addr, align 8
  %i3 = load i64, i64* %__size.addr, align 8
  %i4 = load i64, i64* %__align_val, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvmSt11align_val_t(i8* %i2, i64 %i3, i64 %i4)
  br label %return

if.else:                                          ; preds = %entry
  %i5 = load i8*, i8** %__ptr.addr, align 8
  %i6 = load i64, i64* %__size.addr, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %i5, i64 %i6)
  br label %return

return:                                           ; preds = %if.else, %if.then
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %__align) #0 {
entry:
  %__align.addr = alloca i64, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %cmp = icmp ugt i64 %i, 16
  ret i1 %cmp
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvmSt11align_val_t(i8* %__ptr, i64 %__size, i64 %__align) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  %i1 = load i64, i64* %__align.addr, align 8
  call void @_ZNSt3__117_DeallocateCaller9__do_callISt11align_val_tEEvPvT_(i8* %i, i64 %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %__ptr, i64 %__size) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__size, i64* %__size.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  call void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %i)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callISt11align_val_tEEvPvT_(i8* %__ptr, i64 %__a1) #0 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__a1.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__a1, i64* %__a1.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  %i1 = load i64, i64* %__a1.addr, align 8
  call void @_ZdlPvSt11align_val_t(i8* %i, i64 %i1) #14
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPvSt11align_val_t(i8*, i64) #4

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %__ptr) #0 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  call void @_ZdlPv(i8* %i) #14
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) #4

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #12
  ret i32** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJiEEEvDpOT_(%"class.std::__1::vector"* %this, i32* nonnull align 4 dereferenceable(4) %__args) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__args.addr = alloca i32*, align 8
  %__tx = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i32* %__args, i32** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i) #12
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load i32*, i32** %__pos_, align 8
  %call2 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i1) #12
  %i2 = load i32*, i32** %__args.addr, align 8
  %call3 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i2) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call2, i32* nonnull align 4 dereferenceable(4) %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_4 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load i32*, i32** %__pos_4, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 1
  store i32* %incdec.ptr, i32** %__pos_4, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__14moveIRiEEONS_16remove_referenceIT_E4typeEOS3_(i32* nonnull align 4 dereferenceable(4) %__t) #0 {
entry:
  %__t.addr = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIiEEvOT_(%"class.std::__1::vector"* %this, i32* nonnull align 4 dereferenceable(4) %__x) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca i32*, align 8
  %__a = alloca %"class.std::__1::allocator"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i32* %__x, i32** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i) #12
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this1) #12
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this1) #12
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i3 = load i32*, i32** %__end_, align 8
  %call5 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i3) #12
  %i4 = load i32*, i32** %__x.addr, align 8
  %call6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i4) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2, i32* %call5, i32* nonnull align 4 dereferenceable(4) %call6)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i5 = load i32*, i32** %__end_7, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i5, i32 1
  store i32* %incdec.ptr, i32** %__end_7, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %this1, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont8

invoke.cont8:                                     ; preds = %invoke.cont
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %__v) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #12
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret i32** %__value_
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i, i64 %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %__args.addr = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  store i32* %__args, i32** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load i32*, i32** %__p.addr, align 8
  %i3 = load i32*, i32** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, i32* %i2, i32* nonnull align 4 dereferenceable(4) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  store %"class.std::__1::vector"* %i, %"class.std::__1::vector"** %__v_, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  %i3 = load i32*, i32** %__end_, align 8
  store i32* %i3, i32** %__pos_, align 8
  %__new_end_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 2
  %i4 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i5 = bitcast %"class.std::__1::vector"* %i4 to %"class.std::__1::__vector_base"*
  %__end_2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i5, i32 0, i32 1
  %i6 = load i32*, i32** %__end_2, align 8
  %i7 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr inbounds i32, i32* %i6, i64 %i7
  store i32* %add.ptr, i32** %__new_end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %__args.addr = alloca i32*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  store i32* %__args, i32** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load i32*, i32** %__p.addr, align 8
  %i3 = load i32*, i32** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #12
  call void @_ZNSt3__19allocatorIiE9constructIiJiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %i1, i32* %i2, i32* nonnull align 4 dereferenceable(4) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorIiE9constructIiJiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %this, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %__args.addr = alloca i32*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  store i32* %__args, i32** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load i32*, i32** %__p.addr, align 8
  %i1 = bitcast i32* %i to i8*
  %i2 = bitcast i8* %i1 to i32*
  %i3 = load i32*, i32** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #12
  %i4 = load i32, i32* %call, align 4
  store i32 %i4, i32* %i2, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__pos_, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  store i32* %i, i32** %__end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector"* %this, i64 %__new_size) #1 align 2 {
entry:
  %retval = alloca i64, align 8
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__new_size.addr = alloca i64, align 8
  %__ms = alloca i64, align 8
  %__cap = alloca i64, align 8
  %ref.tmp = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__new_size, i64* %__new_size.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %this1) #12
  store i64 %call, i64* %__ms, align 8
  %i = load i64, i64* %__new_size.addr, align 8
  %i1 = load i64, i64* %__ms, align 8
  %cmp = icmp ugt i64 %i, %i1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i2) #15
  unreachable

if.end:                                           ; preds = %entry
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this1) #12
  store i64 %call2, i64* %__cap, align 8
  %i3 = load i64, i64* %__cap, align 8
  %i4 = load i64, i64* %__ms, align 8
  %div = udiv i64 %i4, 2
  %cmp3 = icmp uge i64 %i3, %div
  br i1 %cmp3, label %if.then4, label %if.end5

if.then4:                                         ; preds = %if.end
  %i5 = load i64, i64* %__ms, align 8
  store i64 %i5, i64* %retval, align 8
  br label %return

if.end5:                                          ; preds = %if.end
  %i6 = load i64, i64* %__cap, align 8
  %mul = mul i64 2, %i6
  store i64 %mul, i64* %ref.tmp, align 8
  %call6 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %__new_size.addr)
  %i7 = load i64, i64* %call6, align 8
  store i64 %i7, i64* %retval, align 8
  br label %return

return:                                           ; preds = %if.end5, %if.then4
  %i8 = load i64, i64* %retval, align 8
  ret i64 %i8
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %i = load i64, i64* %__cap.addr, align 8
  %i1 = load i64, i64* %__start.addr, align 8
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %this1, i64 %i, i64 %i1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector"* %this, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__v.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer"* %__v, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector"* %this1) #12
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i) #12
  %i1 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 0
  %i2 = load i32*, i32** %__begin_, align 8
  %i3 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 1
  %i4 = load i32*, i32** %__end_, align 8
  %i5 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i5, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i2, i32* %i4, i32** nonnull align 8 dereferenceable(8) %__begin_2)
  %i6 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i6, i32 0, i32 0
  %i7 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i7, i32 0, i32 1
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__begin_3, i32** nonnull align 8 dereferenceable(8) %__begin_4) #12
  %i8 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i8, i32 0, i32 1
  %i9 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__end_6 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i9, i32 0, i32 2
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__end_5, i32** nonnull align 8 dereferenceable(8) %__end_6) #12
  %i10 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call7 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base"* %i10) #12
  %i11 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %call8 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i11) #12
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %call7, i32** nonnull align 8 dereferenceable(8) %call8) #12
  %i12 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_9 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i12, i32 0, i32 1
  %i13 = load i32*, i32** %__begin_9, align 8
  %i14 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i14, i32 0, i32 0
  store i32* %i13, i32** %__first_, align 8
  %call10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this1) #12
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %this1, i64 %call10) #12
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this1)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %this) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %this1) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector"* %this) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %ref.tmp = alloca i64, align 8
  %ref.tmp3 = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %i) #12
  %call2 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call) #12
  store i64 %call2, i64* %ref.tmp, align 8
  %call4 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #12
  store i64 %call4, i64* %ref.tmp3, align 8
  %call5 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %ref.tmp3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i64, i64* %call5, align 8
  ret i64 %i1
}

; Function Attrs: noreturn
declare void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"*) #5

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #1 {
entry:
  %__a.addr = alloca i64*, align 8
  %__b.addr = alloca i64*, align 8
  %agg.tmp = alloca %"struct.std::__1::__less", align 1
  store i64* %__a, i64** %__a.addr, align 8
  store i64* %__b, i64** %__b.addr, align 8
  %i = load i64*, i64** %__a.addr, align 8
  %i1 = load i64*, i64** %__b.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %i, i64* nonnull align 8 dereferenceable(8) %i1)
  ret i64* %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #1 {
entry:
  %__a.addr = alloca i64*, align 8
  %__b.addr = alloca i64*, align 8
  %agg.tmp = alloca %"struct.std::__1::__less", align 1
  store i64* %__a, i64** %__a.addr, align 8
  store i64* %__b, i64** %__b.addr, align 8
  %i = load i64*, i64** %__a.addr, align 8
  %i1 = load i64*, i64** %__b.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %i, i64* nonnull align 8 dereferenceable(8) %i1)
  ret i64* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_max_size", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_max_size"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1) #12
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #0 align 2 {
entry:
  %call = call i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #12
  ret i64 %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #1 {
entry:
  %__comp = alloca %"struct.std::__1::__less", align 1
  %__a.addr = alloca i64*, align 8
  %__b.addr = alloca i64*, align 8
  store i64* %__a, i64** %__a.addr, align 8
  store i64* %__b, i64** %__b.addr, align 8
  %i = load i64*, i64** %__b.addr, align 8
  %i1 = load i64*, i64** %__a.addr, align 8
  %call = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %__comp, i64* nonnull align 8 dereferenceable(8) %i, i64* nonnull align 8 dereferenceable(8) %i1)
  br i1 %call, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %i2 = load i64*, i64** %__b.addr, align 8
  br label %cond.end

cond.false:                                       ; preds = %entry
  %i3 = load i64*, i64** %__a.addr, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond-lvalue = phi i64* [ %i2, %cond.true ], [ %i3, %cond.false ]
  ret i64* %cond-lvalue
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %this, i64* nonnull align 8 dereferenceable(8) %__x, i64* nonnull align 8 dereferenceable(8) %__y) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__less"*, align 8
  %__x.addr = alloca i64*, align 8
  %__y.addr = alloca i64*, align 8
  store %"struct.std::__1::__less"* %this, %"struct.std::__1::__less"** %this.addr, align 8
  store i64* %__x, i64** %__x.addr, align 8
  store i64* %__y, i64** %__y.addr, align 8
  %this1 = load %"struct.std::__1::__less"*, %"struct.std::__1::__less"** %this.addr, align 8
  %i = load i64*, i64** %__x.addr, align 8
  %i1 = load i64, i64* %i, align 8
  %i2 = load i64*, i64** %__y.addr, align 8
  %i3 = load i64, i64* %i2, align 8
  %cmp = icmp ult i64 %i1, %i3
  ret i1 %cmp
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %i1) #12
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret i64 4611686018427387903
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #0 align 2 {
entry:
  ret i64 9223372036854775807
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #0 {
entry:
  %__comp = alloca %"struct.std::__1::__less", align 1
  %__a.addr = alloca i64*, align 8
  %__b.addr = alloca i64*, align 8
  store i64* %__a, i64** %__a.addr, align 8
  store i64* %__b, i64** %__b.addr, align 8
  %i = load i64*, i64** %__a.addr, align 8
  %i1 = load i64*, i64** %__b.addr, align 8
  %call = call zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %__comp, i64* nonnull align 8 dereferenceable(8) %i, i64* nonnull align 8 dereferenceable(8) %i1)
  br i1 %call, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %i2 = load i64*, i64** %__b.addr, align 8
  br label %cond.end

cond.false:                                       ; preds = %entry
  %i3 = load i64*, i64** %__a.addr, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond-lvalue = phi i64* [ %i2, %cond.true ], [ %i3, %cond.false ]
  ret i64* %cond-lvalue
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %ref.tmp = alloca i8*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__split_buffer"* %this1 to %"class.std::__1::__split_buffer_common"*
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  store i8* null, i8** %ref.tmp, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load i64, i64* %__cap.addr, align 8
  %cmp = icmp ne i64 %i2, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #12
  %i3 = load i64, i64* %__cap.addr, align 8
  %call2 = call i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i64 %i3)
  br label %cond.end

cond.false:                                       ; preds = %entry
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32* [ %call2, %cond.true ], [ null, %cond.false ]
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  store i32* %cond, i32** %__first_, align 8
  %__first_3 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i4 = load i32*, i32** %__first_3, align 8
  %i5 = load i64, i64* %__start.addr, align 8
  %add.ptr = getelementptr inbounds i32, i32* %i4, i64 %i5
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  store i32* %add.ptr, i32** %__end_, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 1
  store i32* %add.ptr, i32** %__begin_, align 8
  %__first_4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i6 = load i32*, i32** %__first_4, align 8
  %i7 = load i64, i64* %__cap.addr, align 8
  %add.ptr5 = getelementptr inbounds i32, i32* %i6, i64 %i7
  %call6 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #12
  store i32* %add.ptr5, i32** %call6, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i64 %__n) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call i32* @_ZNSt3__19allocatorIiE8allocateEm(%"class.std::__1::allocator"* %i, i64 %i1)
  ret i32* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #12
  ret i32** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #12
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.5"*
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5) #12
  call void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.5"* %i4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t) #0 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__t, %"class.std::__1::allocator"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t.addr, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.5"* %this, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  store %"class.std::__1::allocator"* %__u, %"class.std::__1::allocator"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.5"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i) #12
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__value_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__19allocatorIiE8allocateEm(%"class.std::__1::allocator"* %this, i64 %__n) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %cmp = icmp ugt i64 %i, 4611686018427387903
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str, i64 0, i64 0)) #15
  unreachable

if.end:                                           ; preds = %entry
  %i1 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i1, 4
  %call = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %mul, i64 4)
  %i2 = bitcast i8* %call to i32*
  ret i32* %i2
}

; Function Attrs: noinline noreturn optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__throw_length_errorEPKc(i8* %__msg) #6 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %__msg.addr = alloca i8*, align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store i8* %__msg, i8** %__msg.addr, align 8
  %exception = call i8* @__cxa_allocate_exception(i64 16) #12
  %i = bitcast i8* %exception to %"class.std::length_error"*
  %i1 = load i8*, i8** %__msg.addr, align 8
  call void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %i, i8* %i1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  call void @__cxa_throw(i8* %exception, i8* bitcast (i8** @_ZTISt12length_error to i8*), i8* bitcast (void (%"class.std::length_error"*)* @_ZNSt12length_errorD1Ev to i8*)) #15
  unreachable
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %__size, i64 %__align) #1 {
entry:
  %retval = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  %__align_val = alloca i64, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #12
  br i1 %call, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i1 = load i64, i64* %__align.addr, align 8
  store i64 %i1, i64* %__align_val, align 8
  %i2 = load i64, i64* %__size.addr, align 8
  %i3 = load i64, i64* %__align_val, align 8
  %call1 = call noalias nonnull i8* @_ZnwmSt11align_val_t(i64 %i2, i64 %i3) #16
  %mask = sub i64 %i3, 1
  %ptrint = ptrtoint i8* %call1 to i64
  %maskedptr = and i64 %ptrint, %mask
  %maskcond = icmp eq i64 %maskedptr, 0
  call void @llvm.assume(i1 %maskcond)
  store i8* %call1, i8** %retval, align 8
  br label %return

if.end:                                           ; preds = %entry
  %i4 = load i64, i64* %__size.addr, align 8
  %call2 = call noalias nonnull i8* @_Znwm(i64 %i4) #16
  store i8* %call2, i8** %retval, align 8
  br label %return

return:                                           ; preds = %if.end, %if.then
  %i5 = load i8*, i8** %retval, align 8
  ret i8* %i5
}

declare i8* @__cxa_allocate_exception(i64)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %this, i8* %__s) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::length_error"*, align 8
  %__s.addr = alloca i8*, align 8
  store %"class.std::length_error"* %this, %"class.std::length_error"** %this.addr, align 8
  store i8* %__s, i8** %__s.addr, align 8
  %this1 = load %"class.std::length_error"*, %"class.std::length_error"** %this.addr, align 8
  %i = load i8*, i8** %__s.addr, align 8
  call void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %this1, i8* %i)
  ret void
}

declare void @__cxa_free_exception(i8*)

; Function Attrs: nounwind
declare void @_ZNSt12length_errorD1Ev(%"class.std::length_error"*) unnamed_addr #7

declare void @__cxa_throw(i8*, i8*, i8*)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %this, i8* %__s) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::length_error"*, align 8
  %__s.addr = alloca i8*, align 8
  store %"class.std::length_error"* %this, %"class.std::length_error"** %this.addr, align 8
  store i8* %__s, i8** %__s.addr, align 8
  %this1 = load %"class.std::length_error"*, %"class.std::length_error"** %this.addr, align 8
  %i = bitcast %"class.std::length_error"* %this1 to %"class.std::logic_error"*
  %i1 = load i8*, i8** %__s.addr, align 8
  call void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"* %i, i8* %i1)
  %i2 = bitcast %"class.std::length_error"* %this1 to i32 (...)***
  store i32 (...)** bitcast (i8** getelementptr inbounds ({ [5 x i8*] }, { [5 x i8*] }* @_ZTVSt12length_error, i32 0, inrange i32 0, i32 2) to i32 (...)**), i32 (...)*** %i2, align 8
  ret void
}

declare void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"*, i8*) unnamed_addr #8

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_ZnwmSt11align_val_t(i64, i64) #9

; Function Attrs: nounwind willreturn
declare void @llvm.assume(i1) #10

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #9

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.4"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i, i64 8
  %i1 = bitcast i8* %add.ptr to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i1) #12
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.5"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__value_, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.4"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #12
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %__begin1, i32* %__end1, i32** nonnull align 8 dereferenceable(8) %__end2) #0 align 2 {
entry:
  %.addr = alloca %"class.std::__1::allocator"*, align 8
  %__begin1.addr = alloca i32*, align 8
  %__end1.addr = alloca i32*, align 8
  %__end2.addr = alloca i32**, align 8
  %_Np = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %.addr, align 8
  store i32* %__begin1, i32** %__begin1.addr, align 8
  store i32* %__end1, i32** %__end1.addr, align 8
  store i32** %__end2, i32*** %__end2.addr, align 8
  %i = load i32*, i32** %__end1.addr, align 8
  %i1 = load i32*, i32** %__begin1.addr, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  store i64 %sub.ptr.div, i64* %_Np, align 8
  %i2 = load i64, i64* %_Np, align 8
  %i3 = load i32**, i32*** %__end2.addr, align 8
  %i4 = load i32*, i32** %i3, align 8
  %idx.neg = sub i64 0, %i2
  %add.ptr = getelementptr inbounds i32, i32* %i4, i64 %idx.neg
  store i32* %add.ptr, i32** %i3, align 8
  %i5 = load i64, i64* %_Np, align 8
  %cmp = icmp sgt i64 %i5, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i6 = load i32**, i32*** %__end2.addr, align 8
  %i7 = load i32*, i32** %i6, align 8
  %i8 = bitcast i32* %i7 to i8*
  %i9 = load i32*, i32** %__begin1.addr, align 8
  %i10 = bitcast i32* %i9 to i8*
  %i11 = load i64, i64* %_Np, align 8
  %mul = mul i64 %i11, 4
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i8, i8* align 4 %i10, i64 %mul, i1 false)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__x, i32** nonnull align 8 dereferenceable(8) %__y) #0 {
entry:
  %__x.addr = alloca i32**, align 8
  %__y.addr = alloca i32**, align 8
  %__t = alloca i32*, align 8
  store i32** %__x, i32*** %__x.addr, align 8
  store i32** %__y, i32*** %__y.addr, align 8
  %i = load i32**, i32*** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i) #12
  %i1 = load i32*, i32** %call, align 8
  store i32* %i1, i32** %__t, align 8
  %i2 = load i32**, i32*** %__y.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i2) #12
  %i3 = load i32*, i32** %call1, align 8
  %i4 = load i32**, i32*** %__x.addr, align 8
  store i32* %i3, i32** %i4, align 8
  %call2 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %__t) #12
  %i5 = load i32*, i32** %call2, align 8
  %i6 = load i32**, i32*** %__y.addr, align 8
  store i32* %i5, i32** %i6, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector"* %this, i64 %__current_size) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__current_size.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__current_size, i64* %__current_size.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %i = bitcast i32* %call to i8*
  %call2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this1) #12
  %add.ptr = getelementptr inbounds i32, i32* %call2, i64 %call3
  %i1 = bitcast i32* %add.ptr to i8*
  %call4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %call5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector"* %this1) #12
  %add.ptr6 = getelementptr inbounds i32, i32* %call4, i64 %call5
  %i2 = bitcast i32* %add.ptr6 to i8*
  %call7 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector"* %this1) #12
  %i3 = load i64, i64* %__current_size.addr, align 8
  %add.ptr8 = getelementptr inbounds i32, i32* %call7, i64 %i3
  %i4 = bitcast i32* %add.ptr8 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i4) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  ret void
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #11

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %__t) #0 {
entry:
  %__t.addr = alloca i32**, align 8
  store i32** %__t, i32*** %__t.addr, align 8
  %i = load i32**, i32*** %__t.addr, align 8
  ret i32** %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %this) unnamed_addr #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %this1) #12
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__first_, align 8
  %tobool = icmp ne i32* %i, null
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #12
  %__first_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__first_2, align 8
  %call3 = call i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %this1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i1, i64 %call3) #12
  br label %if.end

if.end:                                           ; preds = %invoke.cont, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__begin_, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %this1, i32* %i) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #12
  %i = load i32*, i32** %call, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__first_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %this, i32* %__new_last) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__new_last.addr = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.6", align 1
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store i32* %__new_last, i32** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %i = load i32*, i32** %__new_last.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this1, i32* %i) #12
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this, i32* %__new_last) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %i = alloca %"struct.std::__1::integral_constant.6", align 1
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__new_last.addr = alloca i32*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store i32* %__new_last, i32** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load i32*, i32** %__new_last.addr, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  %i2 = load i32*, i32** %__end_, align 8
  %cmp = icmp ne i32* %i1, %i2
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #12
  %__end_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  %i3 = load i32*, i32** %__end_2, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 -1
  store i32* %incdec.ptr, i32** %__end_2, align 8
  %call3 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %incdec.ptr) #12
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #12
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.4"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #12
  ret i32** %call
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone speculatable willreturn }
attributes #3 = { noinline noreturn nounwind }
attributes #4 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { noinline noreturn optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #10 = { nounwind willreturn }
attributes #11 = { argmemonly nounwind willreturn }
attributes #12 = { nounwind }
attributes #13 = { noreturn nounwind }
attributes #14 = { builtin nounwind }
attributes #15 = { noreturn }
attributes #16 = { builtin allocsize(0) }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
