; ModuleID = 'gaudi/darken_blend_8.ll'
source_filename = "gaudi/darken_blend_8.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"*, %"class.std::__1::__compressed_pair.3" }
%"class.std::__1::vector.0" = type { %"class.std::__1::__vector_base.1" }
%"class.std::__1::__vector_base.1" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }
%"class.std::__1::__compressed_pair.3" = type { %"struct.std::__1::__compressed_pair_elem.4" }
%"struct.std::__1::__compressed_pair_elem.4" = type { %"class.std::__1::vector.0"* }
%"struct.std::__1::__default_init_tag" = type { i8 }
%"class.std::__1::__vector_base_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.5" = type { i8 }
%"class.std::__1::allocator.6" = type { i8 }
%"struct.std::__1::integral_constant" = type { i8 }
%"struct.std::__1::__has_destroy" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.2" = type { i8 }
%"class.std::__1::allocator" = type { i8 }
%"struct.std::__1::__has_destroy.8" = type { i8 }
%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction" = type { %"class.std::__1::vector.0"*, i32*, i32* }
%"struct.std::__1::__split_buffer" = type { i32*, i32*, i32*, %"class.std::__1::__compressed_pair.9" }
%"class.std::__1::__compressed_pair.9" = type { %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem.10" }
%"struct.std::__1::__compressed_pair_elem.10" = type { %"class.std::__1::allocator"* }
%"struct.std::__1::__has_construct" = type { i8 }
%"struct.std::__1::__less" = type { i8 }
%"struct.std::__1::__has_max_size" = type { i8 }
%"class.std::__1::__split_buffer_common" = type { i8 }
%"class.std::length_error" = type { %"class.std::logic_error" }
%"class.std::logic_error" = type { %"class.std::exception", %"class.std::__1::__libcpp_refstring" }
%"class.std::exception" = type { i32 (...)** }
%"class.std::__1::__libcpp_refstring" = type { i8* }
%"struct.std::__1::integral_constant.11" = type { i8 }
%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction" = type { %"class.std::__1::vector"*, %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"* }
%"struct.std::__1::__split_buffer.13" = type { %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"*, %"class.std::__1::__compressed_pair.14" }
%"class.std::__1::__compressed_pair.14" = type { %"struct.std::__1::__compressed_pair_elem.4", %"struct.std::__1::__compressed_pair_elem.15" }
%"struct.std::__1::__compressed_pair_elem.15" = type { %"class.std::__1::allocator.6"* }
%"struct.std::__1::__has_construct.12" = type { i8 }
%"struct.std::__1::__has_select_on_container_copy_construction" = type { i8 }
%"struct.std::__1::__has_max_size.16" = type { i8 }
%"struct.std::__1::__has_construct.17" = type { i8 }

@.str = private unnamed_addr constant [68 x i8] c"allocator<T>::allocate(size_t n) 'n' exceeds maximum supported size\00", align 1
@_ZTISt12length_error = external constant i8*
@_ZTVSt12length_error = external unnamed_addr constant { [5 x i8*] }, align 8

; Function Attrs: noinline optnone ssp uwtable
define void @_Z14darken_blend_8NSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEES5_(%"class.std::__1::vector"* noalias sret align 8 %agg.result, %"class.std::__1::vector"* %base, %"class.std::__1::vector"* %active) #0 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %result.ptr = alloca i8*, align 8
  %nrvo = alloca i1, align 1
  %m = alloca i32, align 4
  %n = alloca i32, align 4
  %row = alloca i32, align 4
  %row_vec = alloca %"class.std::__1::vector.0", align 8
  %col = alloca i32, align 4
  %pixel = alloca i32, align 4
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  %i = bitcast %"class.std::__1::vector"* %agg.result to i8*
  store i8* %i, i8** %result.ptr, align 8
  store i1 false, i1* %nrvo, align 1
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEC1Ev(%"class.std::__1::vector"* %agg.result) #11
  %call = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %base) #11
  %conv = trunc i64 %call to i32
  store i32 %conv, i32* %m, align 4
  %call1 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %base, i64 0) #11
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %call1) #11
  %conv3 = trunc i64 %call2 to i32
  store i32 %conv3, i32* %n, align 4
  store i32 0, i32* %row, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc25, %entry
  %i1 = load i32, i32* %row, align 4
  %i2 = load i32, i32* %m, align 4
  %cmp = icmp slt i32 %i1, %i2
  br i1 %cmp, label %for.body, label %for.end27

for.body:                                         ; preds = %for.cond
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector.0"* %row_vec) #11
  store i32 0, i32* %col, align 4
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body
  %i3 = load i32, i32* %col, align 4
  %i4 = load i32, i32* %n, align 4
  %cmp5 = icmp slt i32 %i3, %i4
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %i5 = load i32, i32* %row, align 4
  %conv7 = sext i32 %i5 to i64
  %call8 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %base, i64 %conv7) #11
  %i6 = load i32, i32* %col, align 4
  %conv9 = sext i32 %i6 to i64
  %call10 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector.0"* %call8, i64 %conv9) #11
  %i7 = load i32, i32* %call10, align 4
  %i8 = load i32, i32* %row, align 4
  %conv11 = sext i32 %i8 to i64
  %call12 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %active, i64 %conv11) #11
  %i9 = load i32, i32* %col, align 4
  %conv13 = sext i32 %i9 to i64
  %call14 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector.0"* %call12, i64 %conv13) #11
  %i10 = load i32, i32* %call14, align 4
  %cmp15 = icmp sgt i32 %i7, %i10
  br i1 %cmp15, label %if.then, label %if.else

if.then:                                          ; preds = %for.body6
  %i11 = load i32, i32* %row, align 4
  %conv16 = sext i32 %i11 to i64
  %call17 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %active, i64 %conv16) #11
  %i12 = load i32, i32* %col, align 4
  %conv18 = sext i32 %i12 to i64
  %call19 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector.0"* %call17, i64 %conv18) #11
  %i13 = load i32, i32* %call19, align 4
  store i32 %i13, i32* %pixel, align 4
  br label %if.end

if.else:                                          ; preds = %for.body6
  %i14 = load i32, i32* %row, align 4
  %conv20 = sext i32 %i14 to i64
  %call21 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %base, i64 %conv20) #11
  %i15 = load i32, i32* %col, align 4
  %conv22 = sext i32 %i15 to i64
  %call23 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector.0"* %call21, i64 %conv22) #11
  %i16 = load i32, i32* %call23, align 4
  store i32 %i16, i32* %pixel, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector.0"* %row_vec, i32* nonnull align 4 dereferenceable(4) %pixel)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.end
  br label %for.inc

for.inc:                                          ; preds = %invoke.cont
  %i17 = load i32, i32* %col, align 4
  %inc = add nsw i32 %i17, 1
  store i32 %inc, i32* %col, align 4
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE9push_backERKS3_(%"class.std::__1::vector"* %agg.result, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %row_vec)
  br label %invoke.cont24

invoke.cont24:                                    ; preds = %for.end
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector.0"* %row_vec) #11
  br label %for.inc25

for.inc25:                                        ; preds = %invoke.cont24
  %i18 = load i32, i32* %row, align 4
  %inc26 = add nsw i32 %i18, 1
  store i32 %inc26, i32* %row, align 4
  br label %for.cond

for.end27:                                        ; preds = %for.cond
  store i1 true, i1* %nrvo, align 1
  %nrvo.val = load i1, i1* %nrvo, align 1
  br i1 %nrvo.val, label %nrvo.skipdtor, label %nrvo.unused

nrvo.unused:                                      ; preds = %for.end27
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEED1Ev(%"class.std::__1::vector"* %agg.result) #11
  br label %nrvo.skipdtor

nrvo.skipdtor:                                    ; preds = %nrvo.unused, %for.end27
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEC1Ev(%"class.std::__1::vector"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEC2Ev(%"class.std::__1::vector"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %"class.std::__1::vector.0"* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint %"class.std::__1::vector.0"* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 24
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i1, i64 %i2
  ret %"class.std::__1::vector.0"* %arrayidx
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i2, i32 0, i32 0
  %i3 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev(%"class.std::__1::vector.0"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector.0"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector.0"* %this, i64 %__n) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %i2
  ret i32* %arrayidx
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi(%"class.std::__1::vector.0"* %this, i32* nonnull align 4 dereferenceable(4) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca i32*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i32* %__x, i32** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i2) #11
  %i3 = load i32*, i32** %call, align 8
  %cmp = icmp ne i32* %i1, %i3
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i4 = load i32*, i32** %__x.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector.0"* %this1, i32* nonnull align 4 dereferenceable(4) %i4)
  br label %if.end

if.else:                                          ; preds = %entry
  %i5 = load i32*, i32** %__x.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector.0"* %this1, i32* nonnull align 4 dereferenceable(4) %i5)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE9push_backERKS3_(%"class.std::__1::vector"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE9__end_capEv(%"class.std::__1::__vector_base"* %i2) #11
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call, align 8
  %cmp = icmp ne %"class.std::__1::vector.0"* %i1, %i3
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE22__construct_one_at_endIJRKS3_EEEvDpOT_(%"class.std::__1::vector"* %this1, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i4)
  br label %if.end

if.else:                                          ; preds = %entry
  %i5 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21__push_back_slow_pathIRKS3_EEvOT_(%"class.std::__1::vector"* %this1, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i5)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector.0"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector.0"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEED1Ev(%"class.std::__1::vector"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEED2Ev(%"class.std::__1::vector"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEEC2Ev(%"class.std::__1::vector"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC2Ev(%"class.std::__1::__vector_base"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC2Ev(%"class.std::__1::__vector_base"* %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
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
  store %"class.std::__1::vector.0"* null, %"class.std::__1::vector.0"** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  store %"class.std::__1::vector.0"* null, %"class.std::__1::vector.0"** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  call void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.3"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base_common"*, align 8
  store %"class.std::__1::__vector_base_common"* %this, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base_common"*, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline noreturn nounwind
define linkonce_odr hidden void @__clang_call_terminate(i8* %arg) #2 {
bb:
  %i = call i8* @__cxa_begin_catch(i8* %arg) #11
  call void @_ZSt9terminatev() #12
  unreachable
}

declare i8* @__cxa_begin_catch(i8*)

declare void @_ZSt9terminatev()

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.3"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.3"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.3"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %agg.tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #11
  call void @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.4"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #11
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.5"* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca i8**, align 8
  store i8** %__t, i8*** %__t.addr, align 8
  %i = load i8**, i8*** %__t.addr, align 8
  ret i8** %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.4"* %this, i8** nonnull align 8 dereferenceable(8) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.4"*, align 8
  %__u.addr = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem.4"* %this, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  store i8** %__u, i8*** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.4"*, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.4", %"struct.std::__1::__compressed_pair_elem.4"* %this1, i32 0, i32 0
  %i = load i8**, i8*** %__u.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i) #11
  store %"class.std::__1::vector.0"* null, %"class.std::__1::vector.0"** %__value_, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"struct.std::__1::__default_init_tag"* %__t, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  %i = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  ret %"struct.std::__1::__default_init_tag"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.5"* %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.5"* %this1 to %"class.std::__1::allocator.6"*
  call void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEEC2Ev(%"class.std::__1::allocator.6"* %i1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEEC2Ev(%"class.std::__1::allocator.6"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEED2Ev(%"class.std::__1::vector"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE17__annotate_deleteEv(%"class.std::__1::vector"* %this1) #11
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  call void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEED2Ev(%"class.std::__1::__vector_base"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE17__annotate_deleteEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %i = bitcast %"class.std::__1::vector.0"* %call to i8*
  %call2 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %call3 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this1) #11
  %add.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call2, i64 %call3
  %i1 = bitcast %"class.std::__1::vector.0"* %add.ptr to i8*
  %call4 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %call5 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %this1) #11
  %add.ptr6 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call4, i64 %call5
  %i2 = bitcast %"class.std::__1::vector.0"* %add.ptr6 to i8*
  %call7 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %call8 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this1) #11
  %add.ptr9 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call7, i64 %call8
  %i3 = bitcast %"class.std::__1::vector.0"* %add.ptr9 to i8*
  call void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE31__annotate_contiguous_containerEPKvS7_S7_S7_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i3) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEED2Ev(%"class.std::__1::__vector_base"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %cmp = icmp ne %"class.std::__1::vector.0"* %i, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5clearEv(%"class.std::__1::__vector_base"* %this1) #11
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %this1) #11
  %__begin_2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_2, align 8
  %call3 = call i64 @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE8capacityEv(%"class.std::__1::__vector_base"* %this1) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE10deallocateERS5_PS4_m(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %i1, i64 %call3) #11
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE31__annotate_contiguous_containerEPKvS7_S7_S7_(%"class.std::__1::vector"* %this, i8* %arg, i8* %arg1, i8* %arg2, i8* %arg3) #1 align 2 {
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
define linkonce_odr hidden %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %call = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %i1) #11
  ret %"class.std::__1::vector.0"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call i64 @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE8capacityEv(%"class.std::__1::__vector_base"* %i) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %__p) #1 {
entry:
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  ret %"class.std::__1::vector.0"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE8capacityEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this1) #11
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %"class.std::__1::vector.0"* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %"class.std::__1::vector.0"* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 24
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.3"* %__end_cap_) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %i) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.4"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.4"* %this, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.4"*, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.4", %"struct.std::__1::__compressed_pair_elem.4"* %this1, i32 0, i32 0
  ret %"class.std::__1::vector.0"** %__value_
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5clearEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  call void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE17__destruct_at_endEPS4_(%"class.std::__1::__vector_base"* %this1, %"class.std::__1::vector.0"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE10deallocateERS5_PS4_m(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p, i64 %__n) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE10deallocateEPS3_m(%"class.std::__1::allocator.6"* %i, %"class.std::__1::vector.0"* %i1, i64 %i2) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.3"* %__end_cap_) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE17__destruct_at_endEPS4_(%"class.std::__1::__vector_base"* %this, %"class.std::__1::vector.0"* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  %__new_last.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__soon_to_be_end = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__new_last, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  store %"class.std::__1::vector.0"* %i, %"class.std::__1::vector.0"** %__soon_to_be_end, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__soon_to_be_end, align 8
  %cmp = icmp ne %"class.std::__1::vector.0"* %i1, %i2
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %this1) #11
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__soon_to_be_end, align 8
  %incdec.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i3, i32 -1
  store %"class.std::__1::vector.0"* %incdec.ptr, %"class.std::__1::vector.0"** %__soon_to_be_end, align 8
  %call2 = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %incdec.ptr) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE7destroyIS4_EEvRS5_PT_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %call2)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %__end_3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  store %"class.std::__1::vector.0"* %i4, %"class.std::__1::vector.0"** %__end_3, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE7destroyIS4_EEvRS5_PT_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_destroy", align 1
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i = bitcast %"struct.std::__1::__has_destroy"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9__destroyIS4_EEvNS_17integral_constantIbLb1EEERS5_PT_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1, %"class.std::__1::vector.0"* %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9__destroyIS4_EEvNS_17integral_constantIbLb1EEERS5_PT_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  call void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE7destroyEPS3_(%"class.std::__1::allocator.6"* %i1, %"class.std::__1::vector.0"* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE7destroyEPS3_(%"class.std::__1::allocator.6"* %this, %"class.std::__1::vector.0"* %__p) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev(%"class.std::__1::vector.0"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE10deallocateEPS3_m(%"class.std::__1::allocator.6"* %this, %"class.std::__1::vector.0"* %__p, i64 %__n) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i1 = bitcast %"class.std::__1::vector.0"* %i to i8*
  %i2 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i2, 24
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %i1, i64 %mul, i64 8)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %__ptr, i64 %__size, i64 %__align) #0 {
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
define linkonce_odr hidden void @_ZNSt3__117_DeallocateCaller33__do_deallocate_handle_size_alignEPvmm(i8* %__ptr, i64 %__size, i64 %__align) #0 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  %__align_val = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #11
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
define linkonce_odr hidden zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %__align) #1 {
entry:
  %__align.addr = alloca i64, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %cmp = icmp ugt i64 %i, 16
  ret i1 %cmp
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvmSt11align_val_t(i8* %__ptr, i64 %__size, i64 %__align) #0 align 2 {
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
define linkonce_odr void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %__ptr, i64 %__size) #0 align 2 {
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
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callISt11align_val_tEEvPvT_(i8* %__ptr, i64 %__a1) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__a1.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__a1, i64* %__a1.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  %i1 = load i64, i64* %__a1.addr, align 8
  call void @_ZdlPvSt11align_val_t(i8* %i, i64 %i1) #13
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPvSt11align_val_t(i8*, i64) #3

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %__ptr) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  call void @_ZdlPv(i8* %i) #13
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) #3

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.5"* %this1 to %"class.std::__1::allocator.6"*
  ret %"class.std::__1::allocator.6"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::vector.0"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base.1"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2Ev(%"class.std::__1::__vector_base.1"* %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  %ref.tmp = alloca i8*, align 8
  %ref.tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__vector_base.1"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  store i32* null, i32** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 1
  store i32* null, i32** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
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
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
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
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #11
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.2"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #11
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.2"* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %this, i8** nonnull align 8 dereferenceable(8) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  %__u.addr = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  store i8** %__u, i8*** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  %i = load i8**, i8*** %__u.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i) #11
  store i32* null, i32** %__value_, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.2"* %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %this, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.2"* %this1 to %"class.std::__1::allocator"*
  call void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %i1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiEC2Ev(%"class.std::__1::allocator"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEED2Ev(%"class.std::__1::vector.0"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector.0"* %this1) #11
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base.1"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %call = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %i = bitcast i32* %call to i8*
  %call2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this1) #11
  %add.ptr = getelementptr inbounds i32, i32* %call2, i64 %call3
  %i1 = bitcast i32* %add.ptr to i8*
  %call4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %call5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %this1) #11
  %add.ptr6 = getelementptr inbounds i32, i32* %call4, i64 %call5
  %i2 = bitcast i32* %add.ptr6 to i8*
  %call7 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %call8 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this1) #11
  %add.ptr9 = getelementptr inbounds i32, i32* %call7, i64 %call8
  %i3 = bitcast i32* %add.ptr9 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector.0"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i3) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEED2Ev(%"class.std::__1::__vector_base.1"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__begin_, align 8
  %cmp = icmp ne i32* %i, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base.1"* %this1) #11
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %this1) #11
  %__begin_2 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_2, align 8
  %call3 = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base.1"* %this1) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i1, i64 %call3) #11
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector.0"* %this, i8* %arg, i8* %arg1, i8* %arg2, i8* %arg3) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %.addr = alloca i8*, align 8
  %.addr1 = alloca i8*, align 8
  %.addr2 = alloca i8*, align 8
  %.addr3 = alloca i8*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i8* %arg, i8** %.addr, align 8
  store i8* %arg1, i8** %.addr1, align 8
  store i8* %arg2, i8** %.addr2, align 8
  store i8* %arg3, i8** %.addr3, align 8
  %this4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %call = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i1) #11
  ret i32* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base.1"* %i) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %__p) #1 {
entry:
  %__p.addr = alloca i32*, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %i = load i32*, i32** %__p.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %this1) #11
  %i = load i32*, i32** %call, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret i32** %__value_
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE5clearEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__begin_, align 8
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base.1"* %this1, i32* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i64 %__n) #1 align 2 {
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
  call void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %i, i32* %i1, i64 %i2) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE17__destruct_at_endEPi(%"class.std::__1::__vector_base.1"* %this, i32* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  %__new_last.addr = alloca i32*, align 8
  %__soon_to_be_end = alloca i32*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  store i32* %__new_last, i32** %__new_last.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__end_, align 8
  store i32* %i, i32** %__soon_to_be_end, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load i32*, i32** %__new_last.addr, align 8
  %i2 = load i32*, i32** %__soon_to_be_end, align 8
  %cmp = icmp ne i32* %i1, %i2
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %this1) #11
  %i3 = load i32*, i32** %__soon_to_be_end, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 -1
  store i32* %incdec.ptr, i32** %__soon_to_be_end, align 8
  %call2 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %incdec.ptr) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call2)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %i4 = load i32*, i32** %__new_last.addr, align 8
  %__end_3 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 1
  store i32* %i4, i32** %__end_3, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_destroy.8", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %i = bitcast %"struct.std::__1::__has_destroy.8"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load i32*, i32** %__p.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, i32* %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9__destroyIiEEvNS_17integral_constantIbLb1EEERS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p) #0 align 2 {
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
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE7destroyEPi(%"class.std::__1::allocator"* %this, i32* %__p) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca i32*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i32* %__p, i32** %__p.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorIiE10deallocateEPim(%"class.std::__1::allocator"* %this, i32* %__p, i64 %__n) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
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

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.2"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %i) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %this, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.2"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #11
  ret i32** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE22__construct_one_at_endIJRKiEEEvDpOT_(%"class.std::__1::vector.0"* %this, i32* nonnull align 4 dereferenceable(4) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca i32*, align 8
  %__tx = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i32* %__args, i32** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i) #11
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load i32*, i32** %__pos_, align 8
  %call2 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i1) #11
  %i2 = load i32*, i32** %__args.addr, align 8
  %call3 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i2) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call2, i32* nonnull align 4 dereferenceable(4) %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_4 = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load i32*, i32** %__pos_4, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 1
  store i32* %incdec.ptr, i32** %__pos_4, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx) #11
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21__push_back_slow_pathIRKiEEvOT_(%"class.std::__1::vector.0"* %this, i32* nonnull align 4 dereferenceable(4) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca i32*, align 8
  %__a = alloca %"class.std::__1::allocator"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i32* %__x, i32** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i) #11
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %this1) #11
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector.0"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %this1) #11
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i3 = load i32*, i32** %__end_, align 8
  %call5 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %i3) #11
  %i4 = load i32*, i32** %__x.addr, align 8
  %call6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i4) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2, i32* %call5, i32* nonnull align 4 dereferenceable(4) %call6)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_7 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i5 = load i32*, i32** %__end_7, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i5, i32 1
  store i32* %incdec.ptr, i32** %__end_7, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector.0"* %this1, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont8

invoke.cont8:                                     ; preds = %invoke.cont
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %__v) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret i32** %__value_
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__v, %"class.std::__1::vector.0"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__v.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i, i64 %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE9constructIiJRKiEEEvRS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #0 align 2 {
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
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, i32* %i2, i32* nonnull align 4 dereferenceable(4) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %__t) #1 {
entry:
  %__t.addr = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC2ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__v, %"class.std::__1::vector.0"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__v.addr, align 8
  store %"class.std::__1::vector.0"* %i, %"class.std::__1::vector.0"** %__v_, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__v.addr, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %i1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i2, i32 0, i32 1
  %i3 = load i32*, i32** %__end_, align 8
  store i32* %i3, i32** %__pos_, align 8
  %__new_end_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 2
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__v.addr, align 8
  %i5 = bitcast %"class.std::__1::vector.0"* %i4 to %"class.std::__1::__vector_base.1"*
  %__end_2 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i5, i32 0, i32 1
  %i6 = load i32*, i32** %__end_2, align 8
  %i7 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr inbounds i32, i32* %i6, i64 %i7
  store i32* %add.ptr, i32** %__new_end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE11__constructIiJRKiEEEvNS_17integral_constantIbLb1EEERS2_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #0 align 2 {
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
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #11
  call void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %i1, i32* %i2, i32* nonnull align 4 dereferenceable(4) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorIiE9constructIiJRKiEEEvPT_DpOT0_(%"class.std::__1::allocator"* %this, i32* %__p, i32* nonnull align 4 dereferenceable(4) %__args) #1 align 2 {
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
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRKiEEOT_RNS_16remove_referenceIS3_E4typeE(i32* nonnull align 4 dereferenceable(4) %i3) #11
  %i4 = load i32, i32* %call, align 4
  store i32 %i4, i32* %i2, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"*, %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"** %this.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__pos_, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__v_, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %i1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i2, i32 0, i32 1
  store i32* %i, i32** %__end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE11__recommendEm(%"class.std::__1::vector.0"* %this, i64 %__new_size) #0 align 2 {
entry:
  %retval = alloca i64, align 8
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__new_size.addr = alloca i64, align 8
  %__ms = alloca i64, align 8
  %__cap = alloca i64, align 8
  %ref.tmp = alloca i64, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i64 %__new_size, i64* %__new_size.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector.0"* %this1) #11
  store i64 %call, i64* %__ms, align 8
  %i = load i64, i64* %__new_size.addr, align 8
  %i1 = load i64, i64* %__ms, align 8
  %cmp = icmp ugt i64 %i, %i1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i2 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i2) #14
  unreachable

if.end:                                           ; preds = %entry
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this1) #11
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
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC1EmmS3_(%"struct.std::__1::__split_buffer"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
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
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__swap_out_circular_bufferERNS_14__split_bufferIiRS2_EE(%"class.std::__1::vector.0"* %this, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__v.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer"* %__v, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE17__annotate_deleteEv(%"class.std::__1::vector.0"* %this1) #11
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i) #11
  %i1 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i1, i32 0, i32 0
  %i2 = load i32*, i32** %__begin_, align 8
  %i3 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i3, i32 0, i32 1
  %i4 = load i32*, i32** %__end_, align 8
  %i5 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i5, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i2, i32* %i4, i32** nonnull align 8 dereferenceable(8) %__begin_2)
  %i6 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i6, i32 0, i32 0
  %i7 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i7, i32 0, i32 1
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__begin_3, i32** nonnull align 8 dereferenceable(8) %__begin_4) #11
  %i8 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_5 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i8, i32 0, i32 1
  %i9 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__end_6 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i9, i32 0, i32 2
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__end_5, i32** nonnull align 8 dereferenceable(8) %__end_6) #11
  %i10 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call7 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i10) #11
  %i11 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %call8 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i11) #11
  call void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %call7, i32** nonnull align 8 dereferenceable(8) %call8) #11
  %i12 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_9 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i12, i32 0, i32 1
  %i13 = load i32*, i32** %__begin_9, align 8
  %i14 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i14, i32 0, i32 0
  store i32* %i13, i32** %__first_, align 8
  %call10 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %this1) #11
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector.0"* %this1, i64 %call10) #11
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector.0"* %this1)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED1Ev(%"struct.std::__1::__split_buffer"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector.0"* %this) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %ref.tmp = alloca i64, align 8
  %ref.tmp3 = alloca i64, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i) #11
  %call2 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call) #11
  store i64 %call2, i64* %ref.tmp, align 8
  %call4 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #11
  store i64 %call4, i64* %ref.tmp3, align 8
  %call5 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %ref.tmp3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i64, i64* %call5, align 8
  ret i64 %i1
}

; Function Attrs: noreturn
declare void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"*) #4

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #0 {
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
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #0 {
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
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8max_sizeERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_max_size", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_max_size"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #1 align 2 {
entry:
  %call = call i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #11
  ret i64 %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #0 {
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
define linkonce_odr hidden zeroext i1 @_ZNKSt3__16__lessImmEclERKmS3_(%"struct.std::__1::__less"* %this, i64* nonnull align 8 dereferenceable(8) %__x, i64* nonnull align 8 dereferenceable(8) %__y) #1 align 2 {
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
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10__max_sizeENS_17integral_constantIbLb1EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %i1) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorIiE8max_sizeEv(%"class.std::__1::allocator"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret i64 4611686018427387903
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIPiNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.2"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %i) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %this, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.2"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #1 align 2 {
entry:
  ret i64 9223372036854775807
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13maxImNS_6__lessImmEEEERKT_S5_S5_T0_(i64* nonnull align 8 dereferenceable(8) %__a, i64* nonnull align 8 dereferenceable(8) %__b) #1 {
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
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEEC2EmmS3_(%"struct.std::__1::__split_buffer"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
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
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.9"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load i64, i64* %__cap.addr, align 8
  %cmp = icmp ne i64 %i2, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #11
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
  %call6 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #11
  store i32* %add.ptr5, i32** %call6, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC1IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.9"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.9"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.9"* %this, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.9"*, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.9"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i64 %__n) #0 align 2 {
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
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.9"* %__end_cap_) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.9"* %__end_cap_) #11
  ret i32** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEEC2IDnS4_EEOT_OT0_(%"class.std::__1::__compressed_pair.9"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.9"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.9"* %this, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.9"*, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.9"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #11
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.9"* %this1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.10"*
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5) #11
  call void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.10"* %i4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__t, %"class.std::__1::allocator"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t.addr, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EEC2IS3_vEEOT_(%"struct.std::__1::__compressed_pair_elem.10"* %this, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.10"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.10"* %this, %"struct.std::__1::__compressed_pair_elem.10"** %this.addr, align 8
  store %"class.std::__1::allocator"* %__u, %"class.std::__1::allocator"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.10"*, %"struct.std::__1::__compressed_pair_elem.10"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.10", %"struct.std::__1::__compressed_pair_elem.10"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorIiEEEEOT_RNS_16remove_referenceIS4_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i) #11
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__value_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i32* @_ZNSt3__19allocatorIiE8allocateEm(%"class.std::__1::allocator"* %this, i64 %__n) #0 align 2 {
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
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str, i64 0, i64 0)) #14
  unreachable

if.end:                                           ; preds = %entry
  %i1 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i1, 4
  %call = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %mul, i64 4)
  %i2 = bitcast i8* %call to i32*
  ret i32* %i2
}

; Function Attrs: noinline noreturn optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__120__throw_length_errorEPKc(i8* %__msg) #5 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %__msg.addr = alloca i8*, align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store i8* %__msg, i8** %__msg.addr, align 8
  %exception = call i8* @__cxa_allocate_exception(i64 16) #11
  %i = bitcast i8* %exception to %"class.std::length_error"*
  %i1 = load i8*, i8** %__msg.addr, align 8
  call void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %i, i8* %i1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  call void @__cxa_throw(i8* %exception, i8* bitcast (i8** @_ZTISt12length_error to i8*), i8* bitcast (void (%"class.std::length_error"*)* @_ZNSt12length_errorD1Ev to i8*)) #14
  unreachable
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %__size, i64 %__align) #0 {
entry:
  %retval = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  %__align_val = alloca i64, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #11
  br i1 %call, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i1 = load i64, i64* %__align.addr, align 8
  store i64 %i1, i64* %__align_val, align 8
  %i2 = load i64, i64* %__size.addr, align 8
  %i3 = load i64, i64* %__align_val, align 8
  %call1 = call noalias nonnull i8* @_ZnwmSt11align_val_t(i64 %i2, i64 %i3) #15
  %mask = sub i64 %i3, 1
  %ptrint = ptrtoint i8* %call1 to i64
  %maskedptr = and i64 %ptrint, %mask
  %maskcond = icmp eq i64 %maskedptr, 0
  call void @llvm.assume(i1 %maskcond)
  store i8* %call1, i8** %retval, align 8
  br label %return

if.end:                                           ; preds = %entry
  %i4 = load i64, i64* %__size.addr, align 8
  %call2 = call noalias nonnull i8* @_Znwm(i64 %i4) #15
  store i8* %call2, i8** %retval, align 8
  br label %return

return:                                           ; preds = %if.end, %if.then
  %i5 = load i8*, i8** %retval, align 8
  ret i8* %i5
}

declare i8* @__cxa_allocate_exception(i64)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %this, i8* %__s) unnamed_addr #0 align 2 {
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
declare void @_ZNSt12length_errorD1Ev(%"class.std::length_error"*) unnamed_addr #6

declare void @__cxa_throw(i8*, i8*, i8*)

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %this, i8* %__s) unnamed_addr #0 align 2 {
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

declare void @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"*, i8*) unnamed_addr #7

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_ZnwmSt11align_val_t(i64, i64) #8

; Function Attrs: nounwind willreturn
declare void @llvm.assume(i1) #9

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #8

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE6secondEv(%"class.std::__1::__compressed_pair.9"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.9"*, align 8
  store %"class.std::__1::__compressed_pair.9"* %this, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.9"*, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.9"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i, i64 8
  %i1 = bitcast i8* %add.ptr to %"struct.std::__1::__compressed_pair_elem.10"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.10"* %i1) #11
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorIiEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.10"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.10"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.10"* %this, %"struct.std::__1::__compressed_pair_elem.10"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.10"*, %"struct.std::__1::__compressed_pair_elem.10"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.10", %"struct.std::__1::__compressed_pair_elem.10"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__value_, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.9"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.9"*, align 8
  store %"class.std::__1::__compressed_pair.9"* %this, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.9"*, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.9"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE46__construct_backward_with_exception_guaranteesIiEENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PT_S8_EE5valuesr31is_trivially_move_constructibleIS8_EE5valueEvE4typeERS2_S9_S9_RS9_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %__begin1, i32* %__end1, i32** nonnull align 8 dereferenceable(8) %__end2) #1 align 2 {
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
define linkonce_odr hidden void @_ZNSt3__14swapIPiEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS3_EE5valueEvE4typeERS3_S6_(i32** nonnull align 8 dereferenceable(8) %__x, i32** nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca i32**, align 8
  %__y.addr = alloca i32**, align 8
  %__t = alloca i32*, align 8
  store i32** %__x, i32*** %__x.addr, align 8
  store i32** %__y, i32*** %__y.addr, align 8
  %i = load i32**, i32*** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i) #11
  %i1 = load i32*, i32** %call, align 8
  store i32* %i1, i32** %__t, align 8
  %i2 = load i32**, i32*** %__y.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %i2) #11
  %i3 = load i32*, i32** %call1, align 8
  %i4 = load i32**, i32*** %__x.addr, align 8
  store i32* %i3, i32** %i4, align 8
  %call2 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %__t) #11
  %i5 = load i32*, i32** %call2, align 8
  %i6 = load i32**, i32*** %__y.addr, align 8
  store i32* %i5, i32** %i6, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector.0"* %this, i64 %__current_size) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__current_size.addr = alloca i64, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i64 %__current_size, i64* %__current_size.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %call = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %i = bitcast i32* %call to i8*
  %call2 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %call3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this1) #11
  %add.ptr = getelementptr inbounds i32, i32* %call2, i64 %call3
  %i1 = bitcast i32* %add.ptr to i8*
  %call4 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %call5 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8capacityEv(%"class.std::__1::vector.0"* %this1) #11
  %add.ptr6 = getelementptr inbounds i32, i32* %call4, i64 %call5
  %i2 = bitcast i32* %add.ptr6 to i8*
  %call7 = call i32* @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4dataEv(%"class.std::__1::vector.0"* %this1) #11
  %i3 = load i64, i64* %__current_size.addr, align 8
  %add.ptr8 = getelementptr inbounds i32, i32* %call7, i64 %i3
  %i4 = bitcast i32* %add.ptr8 to i8*
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE31__annotate_contiguous_containerEPKvS5_S5_S5_(%"class.std::__1::vector.0"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i4) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  ret void
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #10

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNSt3__14moveIRPiEEONS_16remove_referenceIT_E4typeEOS4_(i32** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca i32**, align 8
  store i32** %__t, i32*** %__t.addr, align 8
  %i = load i32**, i32*** %__t.addr, align 8
  ret i32** %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEED2Ev(%"struct.std::__1::__split_buffer"* %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %this1) #11
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__first_, align 8
  %tobool = icmp ne i32* %i, null
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #11
  %__first_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i1 = load i32*, i32** %__first_2, align 8
  %call3 = call i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %this1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE10deallocateERS2_Pim(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i1, i64 %call3) #11
  br label %if.end

if.end:                                           ; preds = %invoke.cont, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE5clearEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 1
  %i = load i32*, i32** %__begin_, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %this1, i32* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE8capacityEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #11
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
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPi(%"struct.std::__1::__split_buffer"* %this, i32* %__new_last) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__new_last.addr = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.11", align 1
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store i32* %__new_last, i32** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %i = load i32*, i32** %__new_last.addr, align 8
  call void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this1, i32* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE17__destruct_at_endEPiNS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this, i32* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %i = alloca %"struct.std::__1::integral_constant.11", align 1
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
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferIiRNS_9allocatorIiEEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #11
  %__end_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  %i3 = load i32*, i32** %__end_2, align 8
  %incdec.ptr = getelementptr inbounds i32, i32* %i3, i32 -1
  store i32* %incdec.ptr, i32** %__end_2, align 8
  %call3 = call i32* @_ZNSt3__112__to_addressIiEEPT_S2_(i32* %incdec.ptr) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE7destroyIiEEvRS2_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__114__split_bufferIiRNS_9allocatorIiEEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.9"* %__end_cap_) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__117__compressed_pairIPiRNS_9allocatorIiEEE5firstEv(%"class.std::__1::__compressed_pair.9"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.9"*, align 8
  store %"class.std::__1::__compressed_pair.9"* %this, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.9"*, %"class.std::__1::__compressed_pair.9"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.9"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) i32** @_ZNKSt3__122__compressed_pair_elemIPiLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #11
  ret i32** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.3"* %__end_cap_) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE22__construct_one_at_endIJRKS3_EEEvDpOT_(%"class.std::__1::vector"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__tx = alloca %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionC1ERS5_m(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #11
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__pos_, align 8
  %call2 = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %i1) #11
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call3 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i2) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9constructIS4_JRKS4_EEEvRS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %call2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_4 = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__pos_4, align 8
  %incdec.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i3, i32 1
  store %"class.std::__1::vector.0"* %incdec.ptr, %"class.std::__1::vector.0"** %__pos_4, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %__tx) #11
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21__push_back_slow_pathIRKS3_EEvOT_(%"class.std::__1::vector"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__a = alloca %"class.std::__1::allocator.6"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer.13", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #11
  store %"class.std::__1::allocator.6"* %call, %"class.std::__1::allocator.6"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %this1) #11
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE11__recommendEm(%"class.std::__1::vector"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %this1) #11
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC1EmmS6_(%"struct.std::__1::__split_buffer.13"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %__v, i32 0, i32 2
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  %call5 = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %i3) #11
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %call6 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i4) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9constructIS4_JRKS4_EEEvRS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i2, %"class.std::__1::vector.0"* %call5, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call6)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_7 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %__v, i32 0, i32 2
  %i5 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_7, align 8
  %incdec.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i5, i32 1
  store %"class.std::__1::vector.0"* %incdec.ptr, %"class.std::__1::vector.0"** %__end_7, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS3_RS4_EE(%"class.std::__1::vector"* %this1, %"struct.std::__1::__split_buffer.13"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont8

invoke.cont8:                                     ; preds = %invoke.cont
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEED1Ev(%"struct.std::__1::__split_buffer.13"* %__v) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %i) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.4"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.4"* %this, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.4"*, %"struct.std::__1::__compressed_pair_elem.4"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.4", %"struct.std::__1::__compressed_pair_elem.4"* %this1, i32 0, i32 0
  ret %"class.std::__1::vector.0"** %__value_
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionC1ERS5_m(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionC2ERS5_m(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i, i64 %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9constructIS4_JRKS4_EEEvRS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct.12", align 1
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct.12"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE11__constructIS4_JRKS4_EEEvNS_17integral_constantIbLb1EEERS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1, %"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %__t, %"class.std::__1::vector.0"** %__t.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__t.addr, align 8
  ret %"class.std::__1::vector.0"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionC2ERS5_m(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  store %"class.std::__1::vector"* %i, %"class.std::__1::vector"** %__v_, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  store %"class.std::__1::vector.0"* %i3, %"class.std::__1::vector.0"** %__pos_, align 8
  %__new_end_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, i32 0, i32 2
  %i4 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i5 = bitcast %"class.std::__1::vector"* %i4 to %"class.std::__1::__vector_base"*
  %__end_2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i5, i32 0, i32 1
  %i6 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_2, align 8
  %i7 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i6, i64 %i7
  store %"class.std::__1::vector.0"* %add.ptr, %"class.std::__1::vector.0"** %__new_end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE11__constructIS4_JRKS4_EEEvNS_17integral_constantIbLb1EEERS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE9constructIS3_JRKS3_EEEvPT_DpOT0_(%"class.std::__1::allocator.6"* %i1, %"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE9constructIS3_JRKS3_EEEvPT_DpOT0_(%"class.std::__1::allocator.6"* %this, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i1 = bitcast %"class.std::__1::vector.0"* %i to i8*
  %i2 = bitcast i8* %i1 to %"class.std::__1::vector.0"*
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardIRKNS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1ERKS3_(%"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1ERKS3_(%"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2ERKS3_(%"class.std::__1::vector.0"* %this1, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2ERKS3_(%"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) unnamed_addr #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  %ref.tmp = alloca %"class.std::__1::allocator", align 1
  %undef.agg.tmp = alloca %"class.std::__1::allocator", align 1
  %__n = alloca i64, align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %i1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i2) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE37select_on_container_copy_constructionERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call)
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2EOS2_(%"class.std::__1::__vector_base.1"* %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %ref.tmp) #11
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %call2 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector.0"* %i3) #11
  store i64 %call2, i64* %__n, align 8
  %i4 = load i64, i64* %__n, align 8
  %cmp = icmp ugt i64 %i4, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i5 = load i64, i64* %__n, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE11__vallocateEm(%"class.std::__1::vector.0"* %this1, i64 %i5)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  %i6 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i7 = bitcast %"class.std::__1::vector.0"* %i6 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i7, i32 0, i32 0
  %i8 = load i32*, i32** %__begin_, align 8
  %i9 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i10 = bitcast %"class.std::__1::vector.0"* %i9 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i10, i32 0, i32 1
  %i11 = load i32*, i32** %__end_, align 8
  %i12 = load i64, i64* %__n, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE18__construct_at_endIPiEENS_9enable_ifIXsr27__is_cpp17_forward_iteratorIT_EE5valueEvE4typeES7_S7_m(%"class.std::__1::vector.0"* %this1, i32* %i8, i32* %i11, i64 %i12)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  br label %if.end

if.end:                                           ; preds = %invoke.cont3, %entry
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE37select_on_container_copy_constructionERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.11", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_select_on_container_copy_construction", align 1
  %undef.agg.tmp = alloca %"class.std::__1::allocator", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_select_on_container_copy_construction"* %ref.tmp to %"struct.std::__1::integral_constant.11"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE39__select_on_container_copy_constructionENS_17integral_constantIbLb0EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2EOS2_(%"class.std::__1::__vector_base.1"* %this, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.1"*, align 8
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %ref.tmp = alloca i8*, align 8
  store %"class.std::__1::__vector_base.1"* %this, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.1"*, %"class.std::__1::__vector_base.1"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__vector_base.1"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 0
  store i32* null, i32** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 1
  store i32* null, i32** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__14moveIRNS_9allocatorIiEEEEONS_16remove_referenceIT_E4typeEOS5_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1) #11
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnS3_EEOT_OT0_(%"class.std::__1::__compressed_pair"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call)
  br label %invoke.cont2

invoke.cont2:                                     ; preds = %invoke.cont
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE11__vallocateEm(%"class.std::__1::vector.0"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE8max_sizeEv(%"class.std::__1::vector.0"* %this1) #11
  %cmp = icmp ugt i64 %i, %call
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i1 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i1) #14
  unreachable

if.end:                                           ; preds = %entry
  %i2 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i2) #11
  %i3 = load i64, i64* %__n.addr, align 8
  %call3 = call i32* @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE8allocateERS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2, i64 %i3)
  %i4 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i4, i32 0, i32 1
  store i32* %call3, i32** %__end_, align 8
  %i5 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i5, i32 0, i32 0
  store i32* %call3, i32** %__begin_, align 8
  %i6 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_4 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i6, i32 0, i32 0
  %i7 = load i32*, i32** %__begin_4, align 8
  %i8 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr inbounds i32, i32* %i7, i64 %i8
  %i9 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call5 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i9) #11
  store i32* %add.ptr, i32** %call5, align 8
  call void @_ZNKSt3__16vectorIiNS_9allocatorIiEEE14__annotate_newEm(%"class.std::__1::vector.0"* %this1, i64 0) #11
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorIiNS_9allocatorIiEEE18__construct_at_endIPiEENS_9enable_ifIXsr27__is_cpp17_forward_iteratorIT_EE5valueEvE4typeES7_S7_m(%"class.std::__1::vector.0"* %this, i32* %__first, i32* %__last, i64 %__n) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__first.addr = alloca i32*, align 8
  %__last.addr = alloca i32*, align 8
  %__n.addr = alloca i64, align 8
  %__tx = alloca %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store i32* %__first, i32** %__first.addr, align 8
  store i32* %__last, i32** %__last.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionC1ERS3_m(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %this1, i64 %i)
  %i1 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i1) #11
  %i2 = load i32*, i32** %__first.addr, align 8
  %i3 = load i32*, i32** %__last.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction", %"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE25__construct_range_forwardIiiiiEENS_9enable_ifIXaaaasr31is_trivially_copy_constructibleIT0_EE5valuesr7is_sameIT1_T2_EE5valueooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PS6_RT_EE5valueEvE4typeERS2_PSC_SH_RSB_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, i32* %i2, i32* %i3, i32** nonnull align 8 dereferenceable(8) %__pos_)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<int, std::__1::allocator<int>>::_ConstructTransaction"* %__tx) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE39__select_on_container_copy_constructionENS_17integral_constantIbLb0EEERKS2_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant.11", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__14moveIRNS_9allocatorIiEEEEONS_16remove_referenceIT_E4typeEOS5_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__t, %"class.std::__1::allocator"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t.addr, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC1IDnS3_EEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnS3_EEOT_OT0_(%"class.std::__1::__compressed_pair"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPiNS_9allocatorIiEEEC2IDnS3_EEOT_OT0_(%"class.std::__1::__compressed_pair"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #11
  call void @_ZNSt3__122__compressed_pair_elemIPiLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.2"*
  %i3 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardINS_9allocatorIiEEEEOT_RNS_16remove_referenceIS3_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i3) #11
  call void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2IS2_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %i2, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardINS_9allocatorIiEEEEOT_RNS_16remove_referenceIS3_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__t, %"class.std::__1::allocator"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t.addr, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemINS_9allocatorIiEELi1ELb1EEC2IS2_vEEOT_(%"struct.std::__1::__compressed_pair_elem.2"* %this, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.2"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.2"* %this, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  store %"class.std::__1::allocator"* %__u, %"class.std::__1::allocator"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.2"*, %"struct.std::__1::__compressed_pair_elem.2"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.2"* %this1 to %"class.std::__1::allocator"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardINS_9allocatorIiEEEEOT_RNS_16remove_referenceIS3_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorIiEEE25__construct_range_forwardIiiiiEENS_9enable_ifIXaaaasr31is_trivially_copy_constructibleIT0_EE5valuesr7is_sameIT1_T2_EE5valueooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS2_PS6_RT_EE5valueEvE4typeERS2_PSC_SH_RSB_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, i32* %__begin1, i32* %__end1, i32** nonnull align 8 dereferenceable(8) %__begin2) #1 align 2 {
entry:
  %.addr = alloca %"class.std::__1::allocator"*, align 8
  %__begin1.addr = alloca i32*, align 8
  %__end1.addr = alloca i32*, align 8
  %__begin2.addr = alloca i32**, align 8
  %_Np = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %.addr, align 8
  store i32* %__begin1, i32** %__begin1.addr, align 8
  store i32* %__end1, i32** %__end1.addr, align 8
  store i32** %__begin2, i32*** %__begin2.addr, align 8
  %i = load i32*, i32** %__end1.addr, align 8
  %i1 = load i32*, i32** %__begin1.addr, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  store i64 %sub.ptr.div, i64* %_Np, align 8
  %i2 = load i64, i64* %_Np, align 8
  %cmp = icmp sgt i64 %i2, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i3 = load i32**, i32*** %__begin2.addr, align 8
  %i4 = load i32*, i32** %i3, align 8
  %i5 = bitcast i32* %i4 to i8*
  %i6 = load i32*, i32** %__begin1.addr, align 8
  %i7 = bitcast i32* %i6 to i8*
  %i8 = load i64, i64* %_Np, align 8
  %mul = mul i64 %i8, 4
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i5, i8* align 4 %i7, i64 %mul, i1 false)
  %i9 = load i64, i64* %_Np, align 8
  %i10 = load i32**, i32*** %__begin2.addr, align 8
  %i11 = load i32*, i32** %i10, align 8
  %add.ptr = getelementptr inbounds i32, i32* %i11, i64 %i9
  store i32* %add.ptr, i32** %i10, align 8
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"*, %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"** %this.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__pos_, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction", %"struct.std::__1::vector<std::__1::vector<int, std::__1::allocator<int>>, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int>>>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  store %"class.std::__1::vector.0"* %i, %"class.std::__1::vector.0"** %__end_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE11__recommendEm(%"class.std::__1::vector"* %this, i64 %__new_size) #0 align 2 {
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
  %call = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8max_sizeEv(%"class.std::__1::vector"* %this1) #11
  store i64 %call, i64* %__ms, align 8
  %i = load i64, i64* %__new_size.addr, align 8
  %i1 = load i64, i64* %__ms, align 8
  %cmp = icmp ugt i64 %i, %i1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i2) #14
  unreachable

if.end:                                           ; preds = %entry
  %call2 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this1) #11
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
define linkonce_odr void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC1EmmS6_(%"struct.std::__1::__split_buffer.13"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %i = load i64, i64* %__cap.addr, align 8
  %i1 = load i64, i64* %__start.addr, align 8
  %i2 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC2EmmS6_(%"struct.std::__1::__split_buffer.13"* %this1, i64 %i, i64 %i1, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i2)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS3_RS4_EE(%"class.std::__1::vector"* %this, %"struct.std::__1::__split_buffer.13"* nonnull align 8 dereferenceable(40) %__v) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__v.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer.13"* %__v, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE17__annotate_deleteEv(%"class.std::__1::vector"* %this1) #11
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #11
  %i1 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 0
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  %i3 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 1
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  %i5 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %__begin_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %i5, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE46__construct_backward_with_exception_guaranteesIPS4_EEvRS5_T_SA_RSA_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* %i4, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__begin_2)
  %i6 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i6, i32 0, i32 0
  %i7 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %__begin_4 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %i7, i32 0, i32 1
  call void @_ZNSt3__14swapIPNS_6vectorIiNS_9allocatorIiEEEEEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS7_EE5valueEvE4typeERS7_SA_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__begin_3, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__begin_4) #11
  %i8 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i8, i32 0, i32 1
  %i9 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %__end_6 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %i9, i32 0, i32 2
  call void @_ZNSt3__14swapIPNS_6vectorIiNS_9allocatorIiEEEEEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS7_EE5valueEvE4typeERS7_SA_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__end_5, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__end_6) #11
  %i10 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call7 = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE9__end_capEv(%"class.std::__1::__vector_base"* %i10) #11
  %i11 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %call8 = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE9__end_capEv(%"struct.std::__1::__split_buffer.13"* %i11) #11
  call void @_ZNSt3__14swapIPNS_6vectorIiNS_9allocatorIiEEEEEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS7_EE5valueEvE4typeERS7_SA_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %call7, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %call8) #11
  %i12 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %__begin_9 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %i12, i32 0, i32 1
  %i13 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_9, align 8
  %i14 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %__v.addr, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %i14, i32 0, i32 0
  store %"class.std::__1::vector.0"* %i13, %"class.std::__1::vector.0"** %__first_, align 8
  %call10 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4sizeEv(%"class.std::__1::vector"* %this1) #11
  call void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE14__annotate_newEm(%"class.std::__1::vector"* %this1, i64 %call10) #11
  call void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this1)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEED1Ev(%"struct.std::__1::__split_buffer.13"* %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEED2Ev(%"struct.std::__1::__split_buffer.13"* %this1) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8max_sizeEv(%"class.std::__1::vector"* %this) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %ref.tmp = alloca i64, align 8
  %ref.tmp3 = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #11
  %call2 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE8max_sizeERKS5_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call) #11
  store i64 %call2, i64* %ref.tmp, align 8
  %call4 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #11
  store i64 %call4, i64* %ref.tmp3, align 8
  %call5 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %ref.tmp3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i64, i64* %call5, align 8
  ret i64 %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE8max_sizeERKS5_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_max_size.16", align 1
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_max_size.16"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %call = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE10__max_sizeENS_17integral_constantIbLb1EEERKS5_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__113__vector_baseINS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE7__allocEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.3"* %__end_cap_) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE10__max_sizeENS_17integral_constantIbLb1EEERKS5_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %call = call i64 @_ZNKSt3__19allocatorINS_6vectorIiNS0_IiEEEEE8max_sizeEv(%"class.std::__1::allocator.6"* %i1) #11
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorINS_6vectorIiNS0_IiEEEEE8max_sizeEv(%"class.std::__1::allocator.6"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  ret i64 768614336404564650
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEENS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.3"*, align 8
  store %"class.std::__1::__compressed_pair.3"* %this, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.3"*, %"class.std::__1::__compressed_pair.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.3"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.5"* %this1 to %"class.std::__1::allocator.6"*
  ret %"class.std::__1::allocator.6"* %i
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC2EmmS6_(%"struct.std::__1::__split_buffer.13"* %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %ref.tmp = alloca i8*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__split_buffer.13"* %this1 to %"class.std::__1::__split_buffer_common"*
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 3
  store i8* null, i8** %ref.tmp, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC1IDnS7_EEOT_OT0_(%"class.std::__1::__compressed_pair.14"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load i64, i64* %__cap.addr, align 8
  %cmp = icmp ne i64 %i2, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE7__allocEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  %i3 = load i64, i64* %__cap.addr, align 8
  %call2 = call %"class.std::__1::vector.0"* @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE8allocateERS5_m(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, i64 %i3)
  br label %cond.end

cond.false:                                       ; preds = %entry
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi %"class.std::__1::vector.0"* [ %call2, %cond.true ], [ null, %cond.false ]
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  store %"class.std::__1::vector.0"* %cond, %"class.std::__1::vector.0"** %__first_, align 8
  %__first_3 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__first_3, align 8
  %i5 = load i64, i64* %__start.addr, align 8
  %add.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i4, i64 %i5
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 2
  store %"class.std::__1::vector.0"* %add.ptr, %"class.std::__1::vector.0"** %__end_, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 1
  store %"class.std::__1::vector.0"* %add.ptr, %"class.std::__1::vector.0"** %__begin_, align 8
  %__first_4 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  %i6 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__first_4, align 8
  %i7 = load i64, i64* %__cap.addr, align 8
  %add.ptr5 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i6, i64 %i7
  %call6 = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE9__end_capEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  store %"class.std::__1::vector.0"* %add.ptr5, %"class.std::__1::vector.0"** %call6, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC1IDnS7_EEOT_OT0_(%"class.std::__1::__compressed_pair.14"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.14"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::__compressed_pair.14"* %this, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator.6"* %__t2, %"class.std::__1::allocator.6"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.14"*, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__t2.addr, align 8
  call void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC2IDnS7_EEOT_OT0_(%"class.std::__1::__compressed_pair.14"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1)
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden %"class.std::__1::vector.0"* @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE8allocateERS5_m(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, i64 %__n) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call %"class.std::__1::vector.0"* @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE8allocateEm(%"class.std::__1::allocator.6"* %i, i64 %i1)
  ret %"class.std::__1::vector.0"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE7__allocEv(%"struct.std::__1::__split_buffer.13"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 3
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.14"* %__end_cap_) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE9__end_capEv(%"struct.std::__1::__split_buffer.13"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.14"* %__end_cap_) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEEC2IDnS7_EEOT_OT0_(%"class.std::__1::__compressed_pair.14"* %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.14"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::__compressed_pair.14"* %this, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator.6"* %__t2, %"class.std::__1::allocator.6"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.14"*, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.14"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #11
  call void @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.4"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.14"* %this1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.15"*
  %i5 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__t2.addr, align 8
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__17forwardIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i5) #11
  call void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb0EEC2IS6_vEEOT_(%"struct.std::__1::__compressed_pair_elem.15"* %i4, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call2)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__17forwardIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"class.std::__1::allocator.6"* %__t, %"class.std::__1::allocator.6"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__t.addr, align 8
  ret %"class.std::__1::allocator.6"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb0EEC2IS6_vEEOT_(%"struct.std::__1::__compressed_pair_elem.15"* %this, %"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.15"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator.6"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.15"* %this, %"struct.std::__1::__compressed_pair_elem.15"** %this.addr, align 8
  store %"class.std::__1::allocator.6"* %__u, %"class.std::__1::allocator.6"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.15"*, %"struct.std::__1::__compressed_pair_elem.15"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.15", %"struct.std::__1::__compressed_pair_elem.15"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__17forwardIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEEEEOT_RNS_16remove_referenceIS7_E4typeE(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i) #11
  store %"class.std::__1::allocator.6"* %call, %"class.std::__1::allocator.6"** %__value_, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr hidden %"class.std::__1::vector.0"* @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE8allocateEm(%"class.std::__1::allocator.6"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %cmp = icmp ugt i64 %i, 768614336404564650
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str, i64 0, i64 0)) #14
  unreachable

if.end:                                           ; preds = %entry
  %i1 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i1, 24
  %call = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %mul, i64 8)
  %i2 = bitcast i8* %call to %"class.std::__1::vector.0"*
  ret %"class.std::__1::vector.0"* %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE6secondEv(%"class.std::__1::__compressed_pair.14"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.14"*, align 8
  store %"class.std::__1::__compressed_pair.14"* %this, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.14"*, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.14"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i, i64 8
  %i1 = bitcast i8* %add.ptr to %"struct.std::__1::__compressed_pair_elem.15"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.15"* %i1) #11
  ret %"class.std::__1::allocator.6"* %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorINS_6vectorIiNS1_IiEEEEEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.15"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.15"* %this, %"struct.std::__1::__compressed_pair_elem.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.15"*, %"struct.std::__1::__compressed_pair_elem.15"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.15", %"struct.std::__1::__compressed_pair_elem.15"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__value_, align 8
  ret %"class.std::__1::allocator.6"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.14"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.14"*, align 8
  store %"class.std::__1::__compressed_pair.14"* %this, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.14"*, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.14"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %i) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE46__construct_backward_with_exception_guaranteesIPS4_EEvRS5_T_SA_RSA_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__begin1, %"class.std::__1::vector.0"* %__end1, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__end2) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__begin1.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__end1.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__end2.addr = alloca %"class.std::__1::vector.0"**, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__begin1, %"class.std::__1::vector.0"** %__begin1.addr, align 8
  store %"class.std::__1::vector.0"* %__end1, %"class.std::__1::vector.0"** %__end1.addr, align 8
  store %"class.std::__1::vector.0"** %__end2, %"class.std::__1::vector.0"*** %__end2.addr, align 8
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end1.addr, align 8
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin1.addr, align 8
  %cmp = icmp ne %"class.std::__1::vector.0"* %i, %i1
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %i2 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i3 = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__end2.addr, align 8
  %i4 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %i3, align 8
  %add.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i4, i64 -1
  %call = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %add.ptr) #11
  %i5 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end1.addr, align 8
  %incdec.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i5, i32 -1
  store %"class.std::__1::vector.0"* %incdec.ptr, %"class.std::__1::vector.0"** %__end1.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__116move_if_noexceptINS_6vectorIiNS_9allocatorIiEEEEEENS_11conditionalIXaantsr29is_nothrow_move_constructibleIT_EE5valuesr21is_copy_constructibleIS6_EE5valueERKS6_OS6_E4typeERS6_(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %incdec.ptr) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9constructIS4_JS4_EEEvRS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i2, %"class.std::__1::vector.0"* %call, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call1)
  %i6 = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__end2.addr, align 8
  %i7 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %i6, align 8
  %incdec.ptr2 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i7, i32 -1
  store %"class.std::__1::vector.0"* %incdec.ptr2, %"class.std::__1::vector.0"** %i6, align 8
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIPNS_6vectorIiNS_9allocatorIiEEEEEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS7_EE5valueEvE4typeERS7_SA_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__x, %"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca %"class.std::__1::vector.0"**, align 8
  %__y.addr = alloca %"class.std::__1::vector.0"**, align 8
  %__t = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"** %__x, %"class.std::__1::vector.0"*** %__x.addr, align 8
  store %"class.std::__1::vector.0"** %__y, %"class.std::__1::vector.0"*** %__y.addr, align 8
  %i = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__14moveIRPNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS8_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %i) #11
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call, align 8
  store %"class.std::__1::vector.0"* %i1, %"class.std::__1::vector.0"** %__t, align 8
  %i2 = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__y.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__14moveIRPNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS8_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %i2) #11
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call1, align 8
  %i4 = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__x.addr, align 8
  store %"class.std::__1::vector.0"* %i3, %"class.std::__1::vector.0"** %i4, align 8
  %call2 = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__14moveIRPNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS8_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__t) #11
  %i5 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call2, align 8
  %i6 = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__y.addr, align 8
  store %"class.std::__1::vector.0"* %i5, %"class.std::__1::vector.0"** %i6, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE14__annotate_newEm(%"class.std::__1::vector"* %this, i64 %__current_size) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__current_size.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__current_size, i64* %__current_size.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %i = bitcast %"class.std::__1::vector.0"* %call to i8*
  %call2 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %call3 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this1) #11
  %add.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call2, i64 %call3
  %i1 = bitcast %"class.std::__1::vector.0"* %add.ptr to i8*
  %call4 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %call5 = call i64 @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE8capacityEv(%"class.std::__1::vector"* %this1) #11
  %add.ptr6 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call4, i64 %call5
  %i2 = bitcast %"class.std::__1::vector.0"* %add.ptr6 to i8*
  %call7 = call %"class.std::__1::vector.0"* @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE4dataEv(%"class.std::__1::vector"* %this1) #11
  %i3 = load i64, i64* %__current_size.addr, align 8
  %add.ptr8 = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %call7, i64 %i3
  %i4 = bitcast %"class.std::__1::vector.0"* %add.ptr8 to i8*
  call void @_ZNKSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE31__annotate_contiguous_containerEPKvS7_S7_S7_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i4) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorINS0_IiNS_9allocatorIiEEEENS1_IS3_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE9constructIS4_JS4_EEEvRS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct.17", align 1
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct.17"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardINS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE11__constructIS4_JS4_EEEvNS_17integral_constantIbLb1EEERS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %i1, %"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__116move_if_noexceptINS_6vectorIiNS_9allocatorIiEEEEEENS_11conditionalIXaantsr29is_nothrow_move_constructibleIT_EE5valuesr21is_copy_constructibleIS6_EE5valueERKS6_OS6_E4typeERS6_(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) #1 {
entry:
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__14moveIRNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS7_(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i) #11
  ret %"class.std::__1::vector.0"* %call
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE11__constructIS4_JS4_EEEvNS_17integral_constantIbLb1EEERS5_PT_DpOT0_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %__a, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %__a, %"class.std::__1::allocator.6"** %__a.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %__a.addr, align 8
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardINS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE9constructIS3_JS3_EEEvPT_DpOT0_(%"class.std::__1::allocator.6"* %i1, %"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardINS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %__t, %"class.std::__1::vector.0"** %__t.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__t.addr, align 8
  ret %"class.std::__1::vector.0"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__19allocatorINS_6vectorIiNS0_IiEEEEE9constructIS3_JS3_EEEvPT_DpOT0_(%"class.std::__1::allocator.6"* %this, %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__args) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.6"*, align 8
  %__p.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__args.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::allocator.6"* %this, %"class.std::__1::allocator.6"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__p, %"class.std::__1::vector.0"** %__p.addr, align 8
  store %"class.std::__1::vector.0"* %__args, %"class.std::__1::vector.0"** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator.6"*, %"class.std::__1::allocator.6"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__p.addr, align 8
  %i1 = bitcast %"class.std::__1::vector.0"* %i to i8*
  %i2 = bitcast i8* %i1 to %"class.std::__1::vector.0"*
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__args.addr, align 8
  %call = call nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__17forwardINS_6vectorIiNS_9allocatorIiEEEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i3) #11
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1EOS3_(%"class.std::__1::vector.0"* %i2, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %call) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC1EOS3_(%"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  call void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2EOS3_(%"class.std::__1::vector.0"* %this1, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorIiNS_9allocatorIiEEEC2EOS3_(%"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__x) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.0"*, align 8
  %__x.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %this, %"class.std::__1::vector.0"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__x, %"class.std::__1::vector.0"** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i2 = bitcast %"class.std::__1::vector.0"* %i1 to %"class.std::__1::__vector_base.1"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE7__allocEv(%"class.std::__1::__vector_base.1"* %i2) #11
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__14moveIRNS_9allocatorIiEEEEONS_16remove_referenceIT_E4typeEOS5_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call) #11
  call void @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEEC2EOS2_(%"class.std::__1::__vector_base.1"* %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2) #11
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i4 = bitcast %"class.std::__1::vector.0"* %i3 to %"class.std::__1::__vector_base.1"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i4, i32 0, i32 0
  %i5 = load i32*, i32** %__begin_, align 8
  %i6 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i6, i32 0, i32 0
  store i32* %i5, i32** %__begin_3, align 8
  %i7 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i8 = bitcast %"class.std::__1::vector.0"* %i7 to %"class.std::__1::__vector_base.1"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i8, i32 0, i32 1
  %i9 = load i32*, i32** %__end_, align 8
  %i10 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %__end_4 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i10, i32 0, i32 1
  store i32* %i9, i32** %__end_4, align 8
  %i11 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i12 = bitcast %"class.std::__1::vector.0"* %i11 to %"class.std::__1::__vector_base.1"*
  %call5 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i12) #11
  %i13 = load i32*, i32** %call5, align 8
  %i14 = bitcast %"class.std::__1::vector.0"* %this1 to %"class.std::__1::__vector_base.1"*
  %call6 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i14) #11
  store i32* %i13, i32** %call6, align 8
  %i15 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i16 = bitcast %"class.std::__1::vector.0"* %i15 to %"class.std::__1::__vector_base.1"*
  %call7 = call nonnull align 8 dereferenceable(8) i32** @_ZNSt3__113__vector_baseIiNS_9allocatorIiEEE9__end_capEv(%"class.std::__1::__vector_base.1"* %i16) #11
  store i32* null, i32** %call7, align 8
  %i17 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i18 = bitcast %"class.std::__1::vector.0"* %i17 to %"class.std::__1::__vector_base.1"*
  %__end_8 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i18, i32 0, i32 1
  store i32* null, i32** %__end_8, align 8
  %i19 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__x.addr, align 8
  %i20 = bitcast %"class.std::__1::vector.0"* %i19 to %"class.std::__1::__vector_base.1"*
  %__begin_9 = getelementptr inbounds %"class.std::__1::__vector_base.1", %"class.std::__1::__vector_base.1"* %i20, i32 0, i32 0
  store i32* null, i32** %__begin_9, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"class.std::__1::vector.0"* @_ZNSt3__14moveIRNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS7_(%"class.std::__1::vector.0"* nonnull align 8 dereferenceable(24) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"class.std::__1::vector.0"* %__t, %"class.std::__1::vector.0"** %__t.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__t.addr, align 8
  ret %"class.std::__1::vector.0"* %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNSt3__14moveIRPNS_6vectorIiNS_9allocatorIiEEEEEEONS_16remove_referenceIT_E4typeEOS8_(%"class.std::__1::vector.0"** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::vector.0"**, align 8
  store %"class.std::__1::vector.0"** %__t, %"class.std::__1::vector.0"*** %__t.addr, align 8
  %i = load %"class.std::__1::vector.0"**, %"class.std::__1::vector.0"*** %__t.addr, align 8
  ret %"class.std::__1::vector.0"** %i
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEED2Ev(%"struct.std::__1::__split_buffer.13"* %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5clearEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__first_, align 8
  %tobool = icmp ne %"class.std::__1::vector.0"* %i, null
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE7__allocEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  %__first_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__first_2, align 8
  %call3 = call i64 @_ZNKSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE8capacityEv(%"struct.std::__1::__split_buffer.13"* %this1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE10deallocateERS5_PS4_m(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %i1, i64 %call3) #11
  br label %if.end

if.end:                                           ; preds = %invoke.cont, %entry
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5clearEv(%"struct.std::__1::__split_buffer.13"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 1
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__begin_, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE17__destruct_at_endEPS4_(%"struct.std::__1::__split_buffer.13"* %this1, %"class.std::__1::vector.0"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE8capacityEv(%"struct.std::__1::__split_buffer.13"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE9__end_capEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %call, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__first_, align 8
  %sub.ptr.lhs.cast = ptrtoint %"class.std::__1::vector.0"* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %"class.std::__1::vector.0"* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 24
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE17__destruct_at_endEPS4_(%"struct.std::__1::__split_buffer.13"* %this, %"class.std::__1::vector.0"* %__new_last) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  %__new_last.addr = alloca %"class.std::__1::vector.0"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.11", align 1
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__new_last, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %i = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  call void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE17__destruct_at_endEPS4_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer.13"* %this1, %"class.std::__1::vector.0"* %i) #11
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE17__destruct_at_endEPS4_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer.13"* %this, %"class.std::__1::vector.0"* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %i = alloca %"struct.std::__1::integral_constant.11", align 1
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  %__new_last.addr = alloca %"class.std::__1::vector.0"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  store %"class.std::__1::vector.0"* %__new_last, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__new_last.addr, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 2
  %i2 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_, align 8
  %cmp = icmp ne %"class.std::__1::vector.0"* %i1, %i2
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.6"* @_ZNSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE7__allocEv(%"struct.std::__1::__split_buffer.13"* %this1) #11
  %__end_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 2
  %i3 = load %"class.std::__1::vector.0"*, %"class.std::__1::vector.0"** %__end_2, align 8
  %incdec.ptr = getelementptr inbounds %"class.std::__1::vector.0", %"class.std::__1::vector.0"* %i3, i32 -1
  store %"class.std::__1::vector.0"* %incdec.ptr, %"class.std::__1::vector.0"** %__end_2, align 8
  %call3 = call %"class.std::__1::vector.0"* @_ZNSt3__112__to_addressINS_6vectorIiNS_9allocatorIiEEEEEEPT_S6_(%"class.std::__1::vector.0"* %incdec.ptr) #11
  call void @_ZNSt3__116allocator_traitsINS_9allocatorINS_6vectorIiNS1_IiEEEEEEE7destroyIS4_EEvRS5_PT_(%"class.std::__1::allocator.6"* nonnull align 1 dereferenceable(1) %call, %"class.std::__1::vector.0"* %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__114__split_bufferINS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE9__end_capEv(%"struct.std::__1::__split_buffer.13"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.13"*, align 8
  store %"struct.std::__1::__split_buffer.13"* %this, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.13"*, %"struct.std::__1::__split_buffer.13"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.13", %"struct.std::__1::__split_buffer.13"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.14"* %__end_cap_) #11
  ret %"class.std::__1::vector.0"** %call
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__117__compressed_pairIPNS_6vectorIiNS_9allocatorIiEEEERNS2_IS4_EEE5firstEv(%"class.std::__1::__compressed_pair.14"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.14"*, align 8
  store %"class.std::__1::__compressed_pair.14"* %this, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.14"*, %"class.std::__1::__compressed_pair.14"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.14"* %this1 to %"struct.std::__1::__compressed_pair_elem.4"*
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::vector.0"** @_ZNKSt3__122__compressed_pair_elemIPNS_6vectorIiNS_9allocatorIiEEEELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.4"* %i) #11
  ret %"class.std::__1::vector.0"** %call
}

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline noreturn nounwind }
attributes #3 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noinline noreturn optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { nounwind willreturn }
attributes #10 = { argmemonly nounwind willreturn }
attributes #11 = { nounwind }
attributes #12 = { noreturn nounwind }
attributes #13 = { builtin nounwind }
attributes #14 = { noreturn }
attributes #15 = { builtin allocsize(0) }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
