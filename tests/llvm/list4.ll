; ModuleID = 'list4.ll'
source_filename = "list4.cc"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

%"class.std::__1::basic_ostream" = type { i32 (...)**, %"class.std::__1::basic_ios.base" }
%"class.std::__1::basic_ios.base" = type <{ %"class.std::__1::ios_base", %"class.std::__1::basic_ostream"*, i32 }>
%"class.std::__1::ios_base" = type { i32 (...)**, i32, i64, i64, i32, i32, i8*, i8*, void (i32, %"class.std::__1::ios_base"*, i32)**, i32*, i64, i64, i64*, i64, i64, i8**, i64, i64 }
%"class.std::__1::locale::id" = type <{ %"struct.std::__1::once_flag", i32, [4 x i8] }>
%"struct.std::__1::once_flag" = type { i64 }
%struct.list = type { %"class.std::__1::vector" }
%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { %struct.User*, %struct.User*, %"class.std::__1::__compressed_pair" }
%struct.User = type { i32, i32 }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { %struct.User* }
%struct.list.1 = type { %"class.std::__1::vector.2" }
%"class.std::__1::vector.2" = type { %"class.std::__1::__vector_base.3" }
%"class.std::__1::__vector_base.3" = type { %struct.Role*, %struct.Role*, %"class.std::__1::__compressed_pair.4" }
%struct.Role = type { i32, i32 }
%"class.std::__1::__compressed_pair.4" = type { %"struct.std::__1::__compressed_pair_elem.5" }
%"struct.std::__1::__compressed_pair_elem.5" = type { %struct.Role* }
%"class.std::__1::__wrap_iter" = type { %struct.User* }
%"class.std::__1::__wrap_iter.9" = type { %struct.User* }
%"class.std::__1::basic_ios" = type <{ %"class.std::__1::ios_base", %"class.std::__1::basic_ostream"*, i32, [4 x i8] }>
%"struct.std::__1::__default_init_tag" = type { i8 }
%"class.std::__1::__vector_base_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.0" = type { i8 }
%"class.std::__1::allocator" = type { i8 }
%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction" = type { %"class.std::__1::vector"*, %struct.User*, %struct.User* }
%"struct.std::__1::__split_buffer" = type { %struct.User*, %struct.User*, %struct.User*, %"class.std::__1::__compressed_pair.10" }
%"class.std::__1::__compressed_pair.10" = type { %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem.11" }
%"struct.std::__1::__compressed_pair_elem.11" = type { %"class.std::__1::allocator"* }
%"struct.std::__1::integral_constant" = type { i8 }
%"struct.std::__1::__has_construct" = type { i8 }
%"struct.std::__1::__less" = type { i8 }
%"struct.std::__1::__has_max_size" = type { i8 }
%"class.std::__1::__split_buffer_common" = type { i8 }
%"class.std::length_error" = type { %"class.std::logic_error" }
%"class.std::logic_error" = type { %"class.std::exception", %"class.std::__1::__libcpp_refstring" }
%"class.std::exception" = type { i32 (...)** }
%"class.std::__1::__libcpp_refstring" = type { i8* }
%"struct.std::__1::integral_constant.12" = type { i8 }
%"struct.std::__1::__has_destroy" = type { i8 }
%"struct.std::__1::__has_construct.13" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.6" = type { i8 }
%"class.std::__1::allocator.7" = type { i8 }
%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction" = type { %"class.std::__1::vector.2"*, %struct.Role*, %struct.Role* }
%"struct.std::__1::__split_buffer.15" = type { %struct.Role*, %struct.Role*, %struct.Role*, %"class.std::__1::__compressed_pair.16" }
%"class.std::__1::__compressed_pair.16" = type { %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.17" }
%"struct.std::__1::__compressed_pair_elem.17" = type { %"class.std::__1::allocator.7"* }
%"struct.std::__1::__has_construct.14" = type { i8 }
%"struct.std::__1::__has_max_size.18" = type { i8 }
%"struct.std::__1::__has_destroy.19" = type { i8 }
%"struct.std::__1::__has_construct.20" = type { i8 }
%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry" = type { i8, %"class.std::__1::basic_ostream"* }
%"class.std::__1::ostreambuf_iterator" = type { %"class.std::__1::basic_streambuf"* }
%"class.std::__1::basic_streambuf" = type { i32 (...)**, %"class.std::__1::locale", i8*, i8*, i8*, i8*, i8*, i8* }
%"class.std::__1::locale" = type { %"class.std::__1::locale::__imp"* }
%"class.std::__1::locale::__imp" = type opaque
%"class.std::__1::basic_string" = type { %"class.std::__1::__compressed_pair.21" }
%"class.std::__1::__compressed_pair.21" = type { %"struct.std::__1::__compressed_pair_elem.22" }
%"struct.std::__1::__compressed_pair_elem.22" = type { %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep" }
%"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep" = type { %union.anon }
%union.anon = type { %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long" }
%"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long" = type { i8*, i64, i64 }
%"class.std::__1::__basic_string_common" = type { i8 }
%"struct.std::__1::__compressed_pair_elem.23" = type { i8 }
%"class.std::__1::allocator.24" = type { i8 }
%"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short" = type { [23 x i8], %struct.anon }
%struct.anon = type { i8 }
%"struct.std::__1::iterator" = type { i8 }
%"class.std::__1::ctype" = type <{ %"class.std::__1::locale::facet", i32*, i8, [7 x i8] }>
%"class.std::__1::locale::facet" = type { %"class.std::__1::__shared_count" }
%"class.std::__1::__shared_count" = type { i32 (...)**, i64 }

@_ZNSt3__14coutE = external global %"class.std::__1::basic_ostream", align 8
@.str = private unnamed_addr constant [5 x i8] c"id: \00", align 1
@.str.1 = private unnamed_addr constant [10 x i8] c" roleId: \00", align 1
@.str.2 = private unnamed_addr constant [68 x i8] c"allocator<T>::allocate(size_t n) 'n' exceeds maximum supported size\00", align 1
@_ZTISt12length_error = external constant i8*
@_ZTVSt12length_error = external unnamed_addr constant { [5 x i8*] }, align 8
@_ZNSt3__15ctypeIcE2idE = external global %"class.std::__1::locale::id", align 8

; Function Attrs: noinline optnone sspstrong uwtable
define %struct.list* @_Z4testP4listI4UserEPS_I4RoleE(%struct.list* %users, %struct.list.1* %roles) #0 {
entry:
  %users.addr = alloca %struct.list*, align 8
  %roles.addr = alloca %struct.list.1*, align 8
  %listUsers = alloca %struct.list*, align 8
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  %ref.tmp = alloca %struct.User, align 4
  %ref.tmp7 = alloca %struct.Role, align 4
  %agg.tmp = alloca %struct.User, align 4
  store %struct.list* %users, %struct.list** %users.addr, align 8
  store %struct.list.1* %roles, %struct.list.1** %roles.addr, align 8
  %call = call %struct.list* @_Z7newListI4UserEP4listIT_Ev()
  store %struct.list* %call, %struct.list** %listUsers, align 8
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc13, %entry
  %i1 = load i32, i32* %i, align 4
  %i2 = load %struct.list*, %struct.list** %users.addr, align 8
  %call1 = call i32 @_Z10listLengthI4UserEiP4listIT_E(%struct.list* %i2)
  %cmp = icmp slt i32 %i1, %call1
  br i1 %cmp, label %bb, label %bb22

for.body:                                         ; preds = %bb
  store i32 0, i32* %j, align 4
  br label %for.cond2

for.cond2:                                        ; preds = %for.inc, %for.body
  %i3 = load i32, i32* %j, align 4
  %i4 = load %struct.list.1*, %struct.list.1** %roles.addr, align 8
  %call3 = call i32 @_Z10listLengthI4RoleEiP4listIT_E(%struct.list.1* %i4)
  %cmp4 = icmp slt i32 %i3, %call3
  br i1 %cmp4, label %bb23, label %bb24

for.body5:                                        ; preds = %bb23
  %i5 = load %struct.list*, %struct.list** %users.addr, align 8
  %i6 = load i32, i32* %i, align 4
  %call6 = call i64 @_Z7listGetI4UserET_P4listIS1_Ei(%struct.list* %i5, i32 %i6)
  %i7 = bitcast %struct.User* %ref.tmp to i64*
  store i64 %call6, i64* %i7, align 4
  %roleId = getelementptr inbounds %struct.User, %struct.User* %ref.tmp, i32 0, i32 1
  %i8 = load i32, i32* %roleId, align 4
  %i9 = load %struct.list.1*, %struct.list.1** %roles.addr, align 8
  %i10 = load i32, i32* %j, align 4
  %call8 = call i64 @_Z7listGetI4RoleET_P4listIS1_Ei(%struct.list.1* %i9, i32 %i10)
  %i11 = bitcast %struct.Role* %ref.tmp7 to i64*
  store i64 %call8, i64* %i11, align 4
  %roleId9 = getelementptr inbounds %struct.Role, %struct.Role* %ref.tmp7, i32 0, i32 0
  %i12 = load i32, i32* %roleId9, align 4
  %cmp10 = icmp eq i32 %i8, %i12
  br i1 %cmp10, label %bb25, label %bb26

if.then:                                          ; preds = %bb25
  %i13 = load %struct.list*, %struct.list** %listUsers, align 8
  %i14 = load %struct.list*, %struct.list** %users.addr, align 8
  %i15 = load i32, i32* %i, align 4
  %call11 = call i64 @_Z7listGetI4UserET_P4listIS1_Ei(%struct.list* %i14, i32 %i15)
  %i16 = bitcast %struct.User* %agg.tmp to i64*
  store i64 %call11, i64* %i16, align 4
  %i17 = bitcast %struct.User* %agg.tmp to i64*
  %i18 = load i64, i64* %i17, align 4
  %call12 = call %struct.list* @_Z10listAppendI4UserEP4listIT_ES4_S2_(%struct.list* %i13, i64 %i18)
  store %struct.list* %call12, %struct.list** %listUsers, align 8
  br label %if.end

if.end:                                           ; preds = %bb26, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %i19 = load i32, i32* %j, align 4
  %inc = add i32 %i19, 1
  store i32 %inc, i32* %j, align 4
  br label %for.cond2

for.end:                                          ; preds = %bb24
  br label %for.inc13

for.inc13:                                        ; preds = %for.end
  %i20 = load i32, i32* %i, align 4
  %inc14 = add i32 %i20, 1
  store i32 %inc14, i32* %i, align 4
  br label %for.cond

for.end15:                                        ; preds = %bb22
  %i21 = load %struct.list*, %struct.list** %listUsers, align 8
  ret %struct.list* %i21

bb:                                               ; preds = %for.cond
  br label %for.body

bb22:                                             ; preds = %for.cond
  br label %for.end15

bb23:                                             ; preds = %for.cond2
  br label %for.body5

bb24:                                             ; preds = %for.cond2
  br label %for.end

bb25:                                             ; preds = %for.body5
  br label %if.then

bb26:                                             ; preds = %for.body5
  br label %if.end
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.list* @_Z7newListI4UserEP4listIT_Ev() #0 {
entry:
  %call = call noalias nonnull i8* @_Znwm(i64 24) #13
  %i = bitcast i8* %call to %struct.list*
  %i1 = bitcast %struct.list* %i to i8*
  call void @llvm.memset.p0i8.i64(i8* align 8 %i1, i8 0, i64 24, i1 false)
  %call1 = call %struct.list* @_ZN4listI4UserEC1Ev(%struct.list* %i) #14
  ret %struct.list* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_Z10listLengthI4UserEiP4listIT_E(%struct.list* %l) #1 {
entry:
  %l.addr = alloca %struct.list*, align 8
  store %struct.list* %l, %struct.list** %l.addr, align 8
  %i = load %struct.list*, %struct.list** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i, i32 0, i32 0
  %call = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %contents) #14
  %conv = trunc i64 %call to i32
  ret i32 %conv
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_Z10listLengthI4RoleEiP4listIT_E(%struct.list.1* %l) #1 {
entry:
  %l.addr = alloca %struct.list.1*, align 8
  store %struct.list.1* %l, %struct.list.1** %l.addr, align 8
  %i = load %struct.list.1*, %struct.list.1** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list.1, %struct.list.1* %i, i32 0, i32 0
  %call = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %contents) #14
  %conv = trunc i64 %call to i32
  ret i32 %conv
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i64 @_Z7listGetI4UserET_P4listIS1_Ei(%struct.list* %l, i32 %i) #1 {
entry:
  %retval = alloca %struct.User, align 4
  %l.addr = alloca %struct.list*, align 8
  %i.addr = alloca i32, align 4
  store %struct.list* %l, %struct.list** %l.addr, align 8
  store i32 %i, i32* %i.addr, align 4
  %i1 = load %struct.list*, %struct.list** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i1, i32 0, i32 0
  %i2 = load i32, i32* %i.addr, align 4
  %conv = sext i32 %i2 to i64
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEixEm(%"class.std::__1::vector"* %contents, i64 %conv) #14
  %i3 = bitcast %struct.User* %retval to i8*
  %i4 = bitcast %struct.User* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i3, i8* align 4 %i4, i64 8, i1 false)
  %i5 = bitcast %struct.User* %retval to i64*
  %i6 = load i64, i64* %i5, align 4
  ret i64 %i6
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i64 @_Z7listGetI4RoleET_P4listIS1_Ei(%struct.list.1* %l, i32 %i) #1 {
entry:
  %retval = alloca %struct.Role, align 4
  %l.addr = alloca %struct.list.1*, align 8
  %i.addr = alloca i32, align 4
  store %struct.list.1* %l, %struct.list.1** %l.addr, align 8
  store i32 %i, i32* %i.addr, align 4
  %i1 = load %struct.list.1*, %struct.list.1** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list.1, %struct.list.1* %i1, i32 0, i32 0
  %i2 = load i32, i32* %i.addr, align 4
  %conv = sext i32 %i2 to i64
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEixEm(%"class.std::__1::vector.2"* %contents, i64 %conv) #14
  %i3 = bitcast %struct.Role* %retval to i8*
  %i4 = bitcast %struct.Role* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i3, i8* align 4 %i4, i64 8, i1 false)
  %i5 = bitcast %struct.Role* %retval to i64*
  %i6 = load i64, i64* %i5, align 4
  ret i64 %i6
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.list* @_Z10listAppendI4UserEP4listIT_ES4_S2_(%struct.list* %in, i64 %e.coerce) #0 {
entry:
  %e = alloca %struct.User, align 4
  %in.addr = alloca %struct.list*, align 8
  %r = alloca %struct.list*, align 8
  %i = alloca i32, align 4
  %ref.tmp = alloca %struct.User, align 4
  %i1 = bitcast %struct.User* %e to i64*
  store i64 %e.coerce, i64* %i1, align 4
  store %struct.list* %in, %struct.list** %in.addr, align 8
  %call = call %struct.list* @_Z7newListI4UserEP4listIT_Ev()
  store %struct.list* %call, %struct.list** %r, align 8
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i2 = load i32, i32* %i, align 4
  %i3 = load %struct.list*, %struct.list** %in.addr, align 8
  %call1 = call i32 @_Z10listLengthI4UserEiP4listIT_E(%struct.list* %i3)
  %cmp = icmp slt i32 %i2, %call1
  br i1 %cmp, label %bb, label %bb11

for.body:                                         ; preds = %bb
  %i4 = load %struct.list*, %struct.list** %r, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i4, i32 0, i32 0
  %i5 = load %struct.list*, %struct.list** %in.addr, align 8
  %i6 = load i32, i32* %i, align 4
  %call2 = call i64 @_Z7listGetI4UserET_P4listIS1_Ei(%struct.list* %i5, i32 %i6)
  %i7 = bitcast %struct.User* %ref.tmp to i64*
  store i64 %call2, i64* %i7, align 4
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE9push_backEOS1_(%"class.std::__1::vector"* %contents, %struct.User* nonnull align 4 dereferenceable(8) %ref.tmp)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %i8 = load i32, i32* %i, align 4
  %inc = add i32 %i8, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %bb11
  %i9 = load %struct.list*, %struct.list** %r, align 8
  %contents3 = getelementptr inbounds %struct.list, %struct.list* %i9, i32 0, i32 0
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE9push_backERKS1_(%"class.std::__1::vector"* %contents3, %struct.User* nonnull align 4 dereferenceable(8) %e)
  %i10 = load %struct.list*, %struct.list** %r, align 8
  ret %struct.list* %i10

bb:                                               ; preds = %for.cond
  br label %for.body

bb11:                                             ; preds = %for.cond
  br label %for.end
}

; Function Attrs: noinline norecurse optnone sspstrong uwtable
define i32 @main(i32 %argc, i8** %argv) #2 {
entry:
  %retval = alloca i32, align 4
  %argc.addr = alloca i32, align 4
  %argv.addr = alloca i8**, align 8
  %users = alloca %struct.list*, align 8
  %u1 = alloca %struct.User, align 4
  %u2 = alloca %struct.User, align 4
  %u3 = alloca %struct.User, align 4
  %agg.tmp = alloca %struct.User, align 4
  %agg.tmp6 = alloca %struct.User, align 4
  %agg.tmp8 = alloca %struct.User, align 4
  %roles = alloca %struct.list.1*, align 8
  %r1 = alloca %struct.Role, align 4
  %r2 = alloca %struct.Role, align 4
  %agg.tmp14 = alloca %struct.Role, align 4
  %agg.tmp16 = alloca %struct.Role, align 4
  %r = alloca %struct.list*, align 8
  %i = alloca %"class.std::__1::__wrap_iter", align 8
  %ref.tmp = alloca %"class.std::__1::__wrap_iter.9", align 8
  %ref.tmp21 = alloca %"class.std::__1::__wrap_iter.9", align 8
  store i32 0, i32* %retval, align 4
  store i32 %argc, i32* %argc.addr, align 4
  store i8** %argv, i8*** %argv.addr, align 8
  %call = call %struct.list* @_Z7newListI4UserEP4listIT_Ev()
  store %struct.list* %call, %struct.list** %users, align 8
  %id = getelementptr inbounds %struct.User, %struct.User* %u1, i32 0, i32 0
  store i32 1, i32* %id, align 4
  %roleId = getelementptr inbounds %struct.User, %struct.User* %u1, i32 0, i32 1
  store i32 1, i32* %roleId, align 4
  %id1 = getelementptr inbounds %struct.User, %struct.User* %u2, i32 0, i32 0
  store i32 2, i32* %id1, align 4
  %roleId2 = getelementptr inbounds %struct.User, %struct.User* %u2, i32 0, i32 1
  store i32 1, i32* %roleId2, align 4
  %id3 = getelementptr inbounds %struct.User, %struct.User* %u3, i32 0, i32 0
  store i32 3, i32* %id3, align 4
  %roleId4 = getelementptr inbounds %struct.User, %struct.User* %u3, i32 0, i32 1
  store i32 3, i32* %roleId4, align 4
  %i1 = load %struct.list*, %struct.list** %users, align 8
  %i2 = bitcast %struct.User* %agg.tmp to i8*
  %i3 = bitcast %struct.User* %u1 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i2, i8* align 4 %i3, i64 8, i1 false)
  %i4 = bitcast %struct.User* %agg.tmp to i64*
  %i5 = load i64, i64* %i4, align 4
  %call5 = call %struct.list* @_Z10listAppendI4UserEP4listIT_ES4_S2_(%struct.list* %i1, i64 %i5)
  store %struct.list* %call5, %struct.list** %users, align 8
  %i6 = load %struct.list*, %struct.list** %users, align 8
  %i7 = bitcast %struct.User* %agg.tmp6 to i8*
  %i8 = bitcast %struct.User* %u2 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i7, i8* align 4 %i8, i64 8, i1 false)
  %i9 = bitcast %struct.User* %agg.tmp6 to i64*
  %i10 = load i64, i64* %i9, align 4
  %call7 = call %struct.list* @_Z10listAppendI4UserEP4listIT_ES4_S2_(%struct.list* %i6, i64 %i10)
  store %struct.list* %call7, %struct.list** %users, align 8
  %i11 = load %struct.list*, %struct.list** %users, align 8
  %i12 = bitcast %struct.User* %agg.tmp8 to i8*
  %i13 = bitcast %struct.User* %u3 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i12, i8* align 4 %i13, i64 8, i1 false)
  %i14 = bitcast %struct.User* %agg.tmp8 to i64*
  %i15 = load i64, i64* %i14, align 4
  %call9 = call %struct.list* @_Z10listAppendI4UserEP4listIT_ES4_S2_(%struct.list* %i11, i64 %i15)
  store %struct.list* %call9, %struct.list** %users, align 8
  %call10 = call %struct.list.1* @_Z7newListI4RoleEP4listIT_Ev()
  store %struct.list.1* %call10, %struct.list.1** %roles, align 8
  %roleId11 = getelementptr inbounds %struct.Role, %struct.Role* %r1, i32 0, i32 0
  store i32 1, i32* %roleId11, align 4
  %name = getelementptr inbounds %struct.Role, %struct.Role* %r1, i32 0, i32 1
  store i32 1, i32* %name, align 4
  %roleId12 = getelementptr inbounds %struct.Role, %struct.Role* %r2, i32 0, i32 0
  store i32 2, i32* %roleId12, align 4
  %name13 = getelementptr inbounds %struct.Role, %struct.Role* %r2, i32 0, i32 1
  store i32 2, i32* %name13, align 4
  %i16 = load %struct.list.1*, %struct.list.1** %roles, align 8
  %i17 = bitcast %struct.Role* %agg.tmp14 to i8*
  %i18 = bitcast %struct.Role* %r1 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i17, i8* align 4 %i18, i64 8, i1 false)
  %i19 = bitcast %struct.Role* %agg.tmp14 to i64*
  %i20 = load i64, i64* %i19, align 4
  %call15 = call %struct.list.1* @_Z10listAppendI4RoleEP4listIT_ES4_S2_(%struct.list.1* %i16, i64 %i20)
  store %struct.list.1* %call15, %struct.list.1** %roles, align 8
  %i21 = load %struct.list.1*, %struct.list.1** %roles, align 8
  %i22 = bitcast %struct.Role* %agg.tmp16 to i8*
  %i23 = bitcast %struct.Role* %r2 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i22, i8* align 4 %i23, i64 8, i1 false)
  %i24 = bitcast %struct.Role* %agg.tmp16 to i64*
  %i25 = load i64, i64* %i24, align 4
  %call17 = call %struct.list.1* @_Z10listAppendI4RoleEP4listIT_ES4_S2_(%struct.list.1* %i21, i64 %i25)
  store %struct.list.1* %call17, %struct.list.1** %roles, align 8
  %i26 = load %struct.list*, %struct.list** %users, align 8
  %i27 = load %struct.list.1*, %struct.list.1** %roles, align 8
  %call18 = call %struct.list* @_Z4testP4listI4UserEPS_I4RoleE(%struct.list* %i26, %struct.list.1* %i27)
  store %struct.list* %call18, %struct.list** %r, align 8
  %i28 = load %struct.list*, %struct.list** %r, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i28, i32 0, i32 0
  %call19 = call i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE5beginEv(%"class.std::__1::vector"* %contents) #14
  %coerce.dive = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %ref.tmp, i32 0, i32 0
  %coerce.val.ip = inttoptr i64 %call19 to %struct.User*
  store %struct.User* %coerce.val.ip, %struct.User** %coerce.dive, align 8
  %call20 = call %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEC1IPS1_EERKNS0_IT_EEPNS_9enable_ifIXsr14is_convertibleIS7_S3_EE5valueEvE4typeE(%"class.std::__1::__wrap_iter"* %i, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %ref.tmp, i8* null) #14
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i29 = load %struct.list*, %struct.list** %r, align 8
  %contents22 = getelementptr inbounds %struct.list, %struct.list* %i29, i32 0, i32 0
  %call23 = call i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE3endEv(%"class.std::__1::vector"* %contents22) #14
  %coerce.dive24 = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %ref.tmp21, i32 0, i32 0
  %coerce.val.ip25 = inttoptr i64 %call23 to %struct.User*
  store %struct.User* %coerce.val.ip25, %struct.User** %coerce.dive24, align 8
  %call26 = call zeroext i1 @_ZNSt3__1neIPK4UserPS1_EEbRKNS_11__wrap_iterIT_EERKNS5_IT0_EE(%"class.std::__1::__wrap_iter"* nonnull align 8 dereferenceable(8) %i, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %ref.tmp21) #14
  br i1 %call26, label %bb, label %bb32

for.body:                                         ; preds = %bb
  %call27 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__1lsINS_11char_traitsIcEEEERNS_13basic_ostreamIcT_EES6_PKc(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) @_ZNSt3__14coutE, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str, i64 0, i64 0))
  %call28 = call %struct.User* @_ZNKSt3__111__wrap_iterIPK4UserEptEv(%"class.std::__1::__wrap_iter"* %i) #14
  %id29 = getelementptr inbounds %struct.User, %struct.User* %call28, i32 0, i32 0
  %i30 = load i32, i32* %id29, align 4
  %call30 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEElsEi(%"class.std::__1::basic_ostream"* %call27, i32 %i30)
  %call31 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__1lsINS_11char_traitsIcEEEERNS_13basic_ostreamIcT_EES6_PKc(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %call30, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.1, i64 0, i64 0))
  %call32 = call %struct.User* @_ZNKSt3__111__wrap_iterIPK4UserEptEv(%"class.std::__1::__wrap_iter"* %i) #14
  %roleId33 = getelementptr inbounds %struct.User, %struct.User* %call32, i32 0, i32 1
  %i31 = load i32, i32* %roleId33, align 4
  %call34 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEElsEi(%"class.std::__1::basic_ostream"* %call31, i32 %i31)
  %call35 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEElsEPFRS3_S4_E(%"class.std::__1::basic_ostream"* %call34, %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)* @_ZNSt3__14endlIcNS_11char_traitsIcEEEERNS_13basic_ostreamIT_T0_EES7_)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %call36 = call nonnull align 8 dereferenceable(8) %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEppEv(%"class.std::__1::__wrap_iter"* %i) #14
  br label %for.cond

for.end:                                          ; preds = %bb32
  ret i32 0

bb:                                               ; preds = %for.cond
  br label %for.body

bb32:                                             ; preds = %for.cond
  br label %for.end
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #3

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.list.1* @_Z7newListI4RoleEP4listIT_Ev() #0 {
entry:
  %call = call noalias nonnull i8* @_Znwm(i64 24) #13
  %i = bitcast i8* %call to %struct.list.1*
  %i1 = bitcast %struct.list.1* %i to i8*
  call void @llvm.memset.p0i8.i64(i8* align 8 %i1, i8 0, i64 24, i1 false)
  %call1 = call %struct.list.1* @_ZN4listI4RoleEC1Ev(%struct.list.1* %i) #14
  ret %struct.list.1* %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.list.1* @_Z10listAppendI4RoleEP4listIT_ES4_S2_(%struct.list.1* %in, i64 %e.coerce) #0 {
entry:
  %e = alloca %struct.Role, align 4
  %in.addr = alloca %struct.list.1*, align 8
  %r = alloca %struct.list.1*, align 8
  %i = alloca i32, align 4
  %ref.tmp = alloca %struct.Role, align 4
  %i1 = bitcast %struct.Role* %e to i64*
  store i64 %e.coerce, i64* %i1, align 4
  store %struct.list.1* %in, %struct.list.1** %in.addr, align 8
  %call = call %struct.list.1* @_Z7newListI4RoleEP4listIT_Ev()
  store %struct.list.1* %call, %struct.list.1** %r, align 8
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i2 = load i32, i32* %i, align 4
  %i3 = load %struct.list.1*, %struct.list.1** %in.addr, align 8
  %call1 = call i32 @_Z10listLengthI4RoleEiP4listIT_E(%struct.list.1* %i3)
  %cmp = icmp slt i32 %i2, %call1
  br i1 %cmp, label %bb, label %bb11

for.body:                                         ; preds = %bb
  %i4 = load %struct.list.1*, %struct.list.1** %r, align 8
  %contents = getelementptr inbounds %struct.list.1, %struct.list.1* %i4, i32 0, i32 0
  %i5 = load %struct.list.1*, %struct.list.1** %in.addr, align 8
  %i6 = load i32, i32* %i, align 4
  %call2 = call i64 @_Z7listGetI4RoleET_P4listIS1_Ei(%struct.list.1* %i5, i32 %i6)
  %i7 = bitcast %struct.Role* %ref.tmp to i64*
  store i64 %call2, i64* %i7, align 4
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE9push_backEOS1_(%"class.std::__1::vector.2"* %contents, %struct.Role* nonnull align 4 dereferenceable(8) %ref.tmp)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %i8 = load i32, i32* %i, align 4
  %inc = add i32 %i8, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %bb11
  %i9 = load %struct.list.1*, %struct.list.1** %r, align 8
  %contents3 = getelementptr inbounds %struct.list.1, %struct.list.1* %i9, i32 0, i32 0
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE9push_backERKS1_(%"class.std::__1::vector.2"* %contents3, %struct.Role* nonnull align 4 dereferenceable(8) %e)
  %i10 = load %struct.list.1*, %struct.list.1** %r, align 8
  ret %struct.list.1* %i10

bb:                                               ; preds = %for.cond
  br label %for.body

bb11:                                             ; preds = %for.cond
  br label %for.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE5beginEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %retval = alloca %"class.std::__1::__wrap_iter.9", align 8
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__begin_, align 8
  %call = call i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE11__make_iterEPS1_(%"class.std::__1::vector"* %this1, %struct.User* %i1) #14
  %coerce.dive = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %retval, i32 0, i32 0
  %coerce.val.ip = inttoptr i64 %call to %struct.User*
  store %struct.User* %coerce.val.ip, %struct.User** %coerce.dive, align 8
  %coerce.dive2 = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %retval, i32 0, i32 0
  %i2 = load %struct.User*, %struct.User** %coerce.dive2, align 8
  %coerce.val.pi = ptrtoint %struct.User* %i2 to i64
  ret i64 %coerce.val.pi
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEC1IPS1_EERKNS0_IT_EEPNS_9enable_ifIXsr14is_convertibleIS7_S3_EE5valueEvE4typeE(%"class.std::__1::__wrap_iter"* returned %this, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %__u, i8* %arg) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  %__u.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  %.addr = alloca i8*, align 8
  store %"class.std::__1::__wrap_iter"* %this, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  store %"class.std::__1::__wrap_iter.9"* %__u, %"class.std::__1::__wrap_iter.9"** %__u.addr, align 8
  store i8* %arg, i8** %.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %i = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %__u.addr, align 8
  %i1 = load i8*, i8** %.addr, align 8
  %call = call %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEC2IPS1_EERKNS0_IT_EEPNS_9enable_ifIXsr14is_convertibleIS7_S3_EE5valueEvE4typeE(%"class.std::__1::__wrap_iter"* %this1, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %i, i8* %i1) #14
  ret %"class.std::__1::__wrap_iter"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNSt3__1neIPK4UserPS1_EEbRKNS_11__wrap_iterIT_EERKNS5_IT0_EE(%"class.std::__1::__wrap_iter"* nonnull align 8 dereferenceable(8) %__x, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  %__y.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  store %"class.std::__1::__wrap_iter"* %__x, %"class.std::__1::__wrap_iter"** %__x.addr, align 8
  store %"class.std::__1::__wrap_iter.9"* %__y, %"class.std::__1::__wrap_iter.9"** %__y.addr, align 8
  %i = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %__x.addr, align 8
  %i1 = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %__y.addr, align 8
  %call = call zeroext i1 @_ZNSt3__1eqIPK4UserPS1_EEbRKNS_11__wrap_iterIT_EERKNS5_IT0_EE(%"class.std::__1::__wrap_iter"* nonnull align 8 dereferenceable(8) %i, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %i1) #14
  %lnot = xor i1 %call, true
  ret i1 %lnot
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE3endEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %retval = alloca %"class.std::__1::__wrap_iter.9", align 8
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__end_, align 8
  %call = call i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE11__make_iterEPS1_(%"class.std::__1::vector"* %this1, %struct.User* %i1) #14
  %coerce.dive = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %retval, i32 0, i32 0
  %coerce.val.ip = inttoptr i64 %call to %struct.User*
  store %struct.User* %coerce.val.ip, %struct.User** %coerce.dive, align 8
  %coerce.dive2 = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %retval, i32 0, i32 0
  %i2 = load %struct.User*, %struct.User** %coerce.dive2, align 8
  %coerce.val.pi = ptrtoint %struct.User* %i2 to i64
  ret i64 %coerce.val.pi
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__1lsINS_11char_traitsIcEEEERNS_13basic_ostreamIcT_EES6_PKc(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %__os, i8* %__str) #0 {
entry:
  %__os.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  %__str.addr = alloca i8*, align 8
  store %"class.std::__1::basic_ostream"* %__os, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  store i8* %__str, i8** %__str.addr, align 8
  %i = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i1 = load i8*, i8** %__str.addr, align 8
  %i2 = load i8*, i8** %__str.addr, align 8
  %call = call i64 @_ZNSt3__111char_traitsIcE6lengthEPKc(i8* %i2) #14
  %call1 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__124__put_character_sequenceIcNS_11char_traitsIcEEEERNS_13basic_ostreamIT_T0_EES7_PKS4_m(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %i, i8* %i1, i64 %call)
  ret %"class.std::__1::basic_ostream"* %call1
}

declare nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEElsEi(%"class.std::__1::basic_ostream"*, i32) #4

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNKSt3__111__wrap_iterIPK4UserEptEv(%"class.std::__1::__wrap_iter"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  store %"class.std::__1::__wrap_iter"* %this, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter", %"class.std::__1::__wrap_iter"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__i, align 8
  %call = call %struct.User* @_ZNSt3__19addressofIK4UserEEPT_RS3_(%struct.User* nonnull align 4 dereferenceable(8) %i) #14
  ret %struct.User* %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEElsEPFRS3_S4_E(%"class.std::__1::basic_ostream"* %this, %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)* %__pf) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  %__pf.addr = alloca %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)*, align 8
  store %"class.std::__1::basic_ostream"* %this, %"class.std::__1::basic_ostream"** %this.addr, align 8
  store %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)* %__pf, %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)** %__pf.addr, align 8
  %this1 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %this.addr, align 8
  %i = load %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)*, %"class.std::__1::basic_ostream"* (%"class.std::__1::basic_ostream"*)** %__pf.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* %i(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %this1)
  ret %"class.std::__1::basic_ostream"* %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__14endlIcNS_11char_traitsIcEEEERNS_13basic_ostreamIT_T0_EES7_(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %__os) #0 {
entry:
  %__os.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  store %"class.std::__1::basic_ostream"* %__os, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i1 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i2 = bitcast %"class.std::__1::basic_ostream"* %i1 to i8**
  %vtable = load i8*, i8** %i2, align 8
  %vbase.offset.ptr = getelementptr i8, i8* %vtable, i64 -24
  %i3 = bitcast i8* %vbase.offset.ptr to i64*
  %vbase.offset = load i64, i64* %i3, align 8
  %i4 = bitcast %"class.std::__1::basic_ostream"* %i1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i4, i64 %vbase.offset
  %i5 = bitcast i8* %add.ptr to %"class.std::__1::basic_ios"*
  %call = call signext i8 @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE5widenEc(%"class.std::__1::basic_ios"* %i5, i8 signext 10)
  %call1 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE3putEc(%"class.std::__1::basic_ostream"* %i, i8 signext %call)
  %i6 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %call2 = call nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE5flushEv(%"class.std::__1::basic_ostream"* %i6)
  %i7 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  ret %"class.std::__1::basic_ostream"* %i7
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEppEv(%"class.std::__1::__wrap_iter"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  store %"class.std::__1::__wrap_iter"* %this, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter", %"class.std::__1::__wrap_iter"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__i, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i, i32 1
  store %struct.User* %incdec.ptr, %struct.User** %__i, align 8
  ret %"class.std::__1::__wrap_iter"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__wrap_iter"* @_ZNSt3__111__wrap_iterIPK4UserEC2IPS1_EERKNS0_IT_EEPNS_9enable_ifIXsr14is_convertibleIS7_S3_EE5valueEvE4typeE(%"class.std::__1::__wrap_iter"* returned %this, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %__u, i8* %arg) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  %__u.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  %.addr = alloca i8*, align 8
  store %"class.std::__1::__wrap_iter"* %this, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  store %"class.std::__1::__wrap_iter.9"* %__u, %"class.std::__1::__wrap_iter.9"** %__u.addr, align 8
  store i8* %arg, i8** %.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter", %"class.std::__1::__wrap_iter"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %__u.addr, align 8
  %call = call %struct.User* @_ZNKSt3__111__wrap_iterIP4UserE4baseEv(%"class.std::__1::__wrap_iter.9"* %i) #14
  store %struct.User* %call, %struct.User** %__i, align 8
  ret %"class.std::__1::__wrap_iter"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNKSt3__111__wrap_iterIP4UserE4baseEv(%"class.std::__1::__wrap_iter.9"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  store %"class.std::__1::__wrap_iter.9"* %this, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__i, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNSt3__1eqIPK4UserPS1_EEbRKNS_11__wrap_iterIT_EERKNS5_IT0_EE(%"class.std::__1::__wrap_iter"* nonnull align 8 dereferenceable(8) %__x, %"class.std::__1::__wrap_iter.9"* nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  %__y.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  store %"class.std::__1::__wrap_iter"* %__x, %"class.std::__1::__wrap_iter"** %__x.addr, align 8
  store %"class.std::__1::__wrap_iter.9"* %__y, %"class.std::__1::__wrap_iter.9"** %__y.addr, align 8
  %i = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %__x.addr, align 8
  %call = call %struct.User* @_ZNKSt3__111__wrap_iterIPK4UserE4baseEv(%"class.std::__1::__wrap_iter"* %i) #14
  %i1 = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %__y.addr, align 8
  %call1 = call %struct.User* @_ZNKSt3__111__wrap_iterIP4UserE4baseEv(%"class.std::__1::__wrap_iter.9"* %i1) #14
  %cmp = icmp eq %struct.User* %call, %call1
  ret i1 %cmp
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNKSt3__111__wrap_iterIPK4UserE4baseEv(%"class.std::__1::__wrap_iter"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter"*, align 8
  store %"class.std::__1::__wrap_iter"* %this, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter"*, %"class.std::__1::__wrap_iter"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter", %"class.std::__1::__wrap_iter"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__i, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNSt3__19addressofIK4UserEEPT_RS3_(%struct.User* nonnull align 4 dereferenceable(8) %__x) #1 {
entry:
  %__x.addr = alloca %struct.User*, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %i = load %struct.User*, %struct.User** %__x.addr, align 8
  ret %struct.User* %i
}

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #5

; Function Attrs: argmemonly nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #6

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.list* @_ZN4listI4UserEC1Ev(%struct.list* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.list*, align 8
  store %struct.list* %this, %struct.list** %this.addr, align 8
  %this1 = load %struct.list*, %struct.list** %this.addr, align 8
  %call = call %struct.list* @_ZN4listI4UserEC2Ev(%struct.list* %this1) #14
  ret %struct.list* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.list* @_ZN4listI4UserEC2Ev(%struct.list* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.list*, align 8
  store %struct.list* %this, %struct.list** %this.addr, align 8
  %this1 = load %struct.list*, %struct.list** %this.addr, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %this1, i32 0, i32 0
  %call = call %"class.std::__1::vector"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEC1Ev(%"class.std::__1::vector"* %contents) #14
  ret %struct.list* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::vector"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEC1Ev(%"class.std::__1::vector"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %"class.std::__1::vector"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::vector"* %this1) #14
  ret %"class.std::__1::vector"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::vector"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::vector"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call %"class.std::__1::__vector_base"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::__vector_base"* %i) #14
  ret %"class.std::__1::vector"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__vector_base"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::__vector_base"* returned %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  %ref.tmp = alloca i8*, align 8
  %ref.tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__vector_base"* %this1 to %"class.std::__1::__vector_base_common"*
  %call = call %"class.std::__1::__vector_base_common"* @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  store %struct.User* null, %struct.User** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 1
  store %struct.User* null, %struct.User** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  %call4 = call %"class.std::__1::__compressed_pair"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  ret %"class.std::__1::__vector_base"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__vector_base_common"* @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base_common"*, align 8
  store %"class.std::__1::__vector_base_common"* %this, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base_common"*, %"class.std::__1::__vector_base_common"** %this.addr, align 8
  ret %"class.std::__1::__vector_base_common"* %this1
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: noinline noreturn nounwind
define linkonce_odr hidden void @__clang_call_terminate(i8* %arg) #7 {
bb:
  %i = call i8* @__cxa_begin_catch(i8* %arg) #14
  call void @_ZSt9terminatev() #15
  unreachable
}

declare i8* @__cxa_begin_catch(i8*)

declare void @_ZSt9terminatev()

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
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
  %call = call %"class.std::__1::__compressed_pair"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1)
  ret %"class.std::__1::__compressed_pair"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
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
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #14
  %call2 = call %"struct.std::__1::__compressed_pair_elem"* @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call3 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #14
  %call4 = call %"struct.std::__1::__compressed_pair_elem.0"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* %i2)
  ret %"class.std::__1::__compressed_pair"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca i8**, align 8
  store i8** %__t, i8*** %__t.addr, align 8
  %i = load i8**, i8*** %__t.addr, align 8
  ret i8** %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__compressed_pair_elem"* @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* returned %this, i8** nonnull align 8 dereferenceable(8) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  %__u.addr = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  store i8** %__u, i8*** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  %i = load i8**, i8*** %__u.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i) #14
  store %struct.User* null, %struct.User** %__value_, align 8
  ret %"struct.std::__1::__compressed_pair_elem"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"struct.std::__1::__default_init_tag"* %__t, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  %i = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t.addr, align 8
  ret %"struct.std::__1::__default_init_tag"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__compressed_pair_elem.0"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.0"* returned %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  %call = call %"class.std::__1::allocator"* @_ZNSt3__19allocatorI4UserEC2Ev(%"class.std::__1::allocator"* %i1) #14
  ret %"struct.std::__1::__compressed_pair_elem.0"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::allocator"* @_ZNSt3__19allocatorI4UserEC2Ev(%"class.std::__1::allocator"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret %"class.std::__1::allocator"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i3 = load %struct.User*, %struct.User** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.User* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.User* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i, i32 0, i32 1
  %i1 = load %struct.Role*, %struct.Role** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i2, i32 0, i32 0
  %i3 = load %struct.Role*, %struct.Role** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.Role* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.Role* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr %struct.User, %struct.User* %i1, i64 %i2
  ret %struct.User* %arrayidx
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEixEm(%"class.std::__1::vector.2"* %this, i64 %__n) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i, i32 0, i32 0
  %i1 = load %struct.Role*, %struct.Role** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr %struct.Role, %struct.Role* %i1, i64 %i2
  ret %struct.Role* %arrayidx
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE9push_backEOS1_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %i2) #14
  %i3 = load %struct.User*, %struct.User** %call, align 8
  %cmp = icmp ult %struct.User* %i1, %i3
  br i1 %cmp, label %bb, label %bb6

if.then:                                          ; preds = %bb
  %i4 = load %struct.User*, %struct.User** %__x.addr, align 8
  %call2 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__14moveIR4UserEEONS_16remove_referenceIT_E4typeEOS4_(%struct.User* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE22__construct_one_at_endIJS1_EEEvDpOT_(%"class.std::__1::vector"* %this1, %struct.User* nonnull align 4 dereferenceable(8) %call2)
  br label %if.end

if.else:                                          ; preds = %bb6
  %i5 = load %struct.User*, %struct.User** %__x.addr, align 8
  %call3 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__14moveIR4UserEEONS_16remove_referenceIT_E4typeEOS4_(%struct.User* nonnull align 4 dereferenceable(8) %i5) #14
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21__push_back_slow_pathIS1_EEvOT_(%"class.std::__1::vector"* %this1, %struct.User* nonnull align 4 dereferenceable(8) %call3)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb6:                                              ; preds = %entry
  br label %if.else
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE9push_backERKS1_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %i2) #14
  %i3 = load %struct.User*, %struct.User** %call, align 8
  %cmp = icmp ne %struct.User* %i1, %i3
  br i1 %cmp, label %bb, label %bb6

if.then:                                          ; preds = %bb
  %i4 = load %struct.User*, %struct.User** %__x.addr, align 8
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE22__construct_one_at_endIJRKS1_EEEvDpOT_(%"class.std::__1::vector"* %this1, %struct.User* nonnull align 4 dereferenceable(8) %i4)
  br label %if.end

if.else:                                          ; preds = %bb6
  %i5 = load %struct.User*, %struct.User** %__x.addr, align 8
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21__push_back_slow_pathIRKS1_EEvOT_(%"class.std::__1::vector"* %this1, %struct.User* nonnull align 4 dereferenceable(8) %i5)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb6:                                              ; preds = %entry
  br label %if.else
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #14
  ret %struct.User** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE22__construct_one_at_endIJS1_EEEvDpOT_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__args.addr = alloca %struct.User*, align 8
  %__tx = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__pos_, align 8
  %call3 = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %i1) #14
  %i2 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call4 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i2) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2, %struct.User* %call3, %struct.User* nonnull align 4 dereferenceable(8) %call4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_5 = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load %struct.User*, %struct.User** %__pos_5, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i3, i32 1
  store %struct.User* %incdec.ptr, %struct.User** %__pos_5, align 8
  %call6 = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__14moveIR4UserEEONS_16remove_referenceIT_E4typeEOS4_(%struct.User* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.User*, align 8
  store %struct.User* %__t, %struct.User** %__t.addr, align 8
  %i = load %struct.User*, %struct.User** %__t.addr, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21__push_back_slow_pathIS1_EEvOT_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  %__a = alloca %"class.std::__1::allocator"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %call5 = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i3 = load %struct.User*, %struct.User** %__end_, align 8
  %call6 = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %i3) #14
  %i4 = load %struct.User*, %struct.User** %__x.addr, align 8
  %call7 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2, %struct.User* %call6, %struct.User* nonnull align 4 dereferenceable(8) %call7)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_8 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i5 = load %struct.User*, %struct.User** %__end_8, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i5, i32 1
  store %struct.User* %incdec.ptr, %struct.User** %__end_8, align 8
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector"* %this1, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont9

invoke.cont9:                                     ; preds = %invoke.cont
  %call10 = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer"* %__v) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #14
  ret %struct.User** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret %struct.User** %__value_
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* returned %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionC2ERS4_m(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %i, i64 %i1)
  ret %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE11__constructIS2_JS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, %struct.User* %i2, %struct.User* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %__p) #1 {
entry:
  %__p.addr = alloca %struct.User*, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.User*, align 8
  store %struct.User* %__t, %struct.User** %__t.addr, align 8
  %i = load %struct.User*, %struct.User** %__t.addr, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1) #14
  ret %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionC2ERS4_m(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* returned %this, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector"* %__v, %"class.std::__1::vector"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  store %"class.std::__1::vector"* %i, %"class.std::__1::vector"** %__v_, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  %i3 = load %struct.User*, %struct.User** %__end_, align 8
  store %struct.User* %i3, %struct.User** %__pos_, align 8
  %__new_end_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, i32 0, i32 2
  %i4 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v.addr, align 8
  %i5 = bitcast %"class.std::__1::vector"* %i4 to %"class.std::__1::__vector_base"*
  %__end_2 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i5, i32 0, i32 1
  %i6 = load %struct.User*, %struct.User** %__end_2, align 8
  %i7 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr %struct.User, %struct.User* %i6, i64 %i7
  store %struct.User* %add.ptr, %struct.User** %__new_end_, align 8
  ret %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE11__constructIS2_JS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__19allocatorI4UserE9constructIS1_JS1_EEEvPT_DpOT0_(%"class.std::__1::allocator"* %i1, %struct.User* %i2, %struct.User* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__19allocatorI4UserE9constructIS1_JS1_EEEvPT_DpOT0_(%"class.std::__1::allocator"* %this, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  %i1 = bitcast %struct.User* %i to i8*
  %i2 = bitcast i8* %i1 to %struct.User*
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardI4UserEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  %i4 = bitcast %struct.User* %i2 to i8*
  %i5 = bitcast %struct.User* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i4, i8* align 4 %i5, i64 8, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"*, %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"** %this.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i = load %struct.User*, %struct.User** %__pos_, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %__v_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %i1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 1
  store %struct.User* %i, %struct.User** %__end_, align 8
  ret %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector"* %this, i64 %__new_size) #0 align 2 {
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
  %call = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8max_sizeEv(%"class.std::__1::vector"* %this1) #14
  store i64 %call, i64* %__ms, align 8
  %i = load i64, i64* %__new_size.addr, align 8
  %i1 = load i64, i64* %__ms, align 8
  %cmp = icmp ugt i64 %i, %i1
  br i1 %cmp, label %bb, label %bb9

if.then:                                          ; preds = %bb
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i2) #16
  unreachable

if.end:                                           ; preds = %bb9
  %call2 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this1) #14
  store i64 %call2, i64* %__cap, align 8
  %i3 = load i64, i64* %__cap, align 8
  %i4 = load i64, i64* %__ms, align 8
  %div = udiv i64 %i4, 2
  %cmp3 = icmp uge i64 %i3, %div
  br i1 %cmp3, label %bb10, label %bb11

if.then4:                                         ; preds = %bb10
  %i5 = load i64, i64* %__ms, align 8
  store i64 %i5, i64* %retval, align 8
  br label %return

if.end5:                                          ; preds = %bb11
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

bb:                                               ; preds = %entry
  br label %if.then

bb9:                                              ; preds = %entry
  br label %if.end

bb10:                                             ; preds = %if.end
  br label %if.then4

bb11:                                             ; preds = %if.end
  br label %if.end5
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer"* returned %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
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
  %call = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEEC2EmmS4_(%"struct.std::__1::__split_buffer"* %this1, i64 %i, i64 %i1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2)
  ret %"struct.std::__1::__split_buffer"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector"* %this, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__v.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer"* %__v, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  call void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE17__annotate_deleteEv(%"class.std::__1::vector"* %this1) #14
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  %i1 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i1, i32 0, i32 0
  %i2 = load %struct.User*, %struct.User** %__begin_, align 8
  %i3 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i3, i32 0, i32 1
  %i4 = load %struct.User*, %struct.User** %__end_, align 8
  %i5 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i5, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE46__construct_backward_with_exception_guaranteesIS2_EENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS3_PT_S9_EE5valuesr31is_trivially_move_constructibleIS9_EE5valueEvE4typeERS3_SA_SA_RSA_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, %struct.User* %i2, %struct.User* %i4, %struct.User** nonnull align 8 dereferenceable(8) %__begin_2)
  %i6 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i6, i32 0, i32 0
  %i7 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i7, i32 0, i32 1
  call void @_ZNSt3__14swapIP4UserEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.User** nonnull align 8 dereferenceable(8) %__begin_3, %struct.User** nonnull align 8 dereferenceable(8) %__begin_4) #14
  %i8 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_5 = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i8, i32 0, i32 1
  %i9 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__end_6 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i9, i32 0, i32 2
  call void @_ZNSt3__14swapIP4UserEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.User** nonnull align 8 dereferenceable(8) %__end_5, %struct.User** nonnull align 8 dereferenceable(8) %__end_6) #14
  %i10 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call7 = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %i10) #14
  %i11 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %call8 = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer"* %i11) #14
  call void @_ZNSt3__14swapIP4UserEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.User** nonnull align 8 dereferenceable(8) %call7, %struct.User** nonnull align 8 dereferenceable(8) %call8) #14
  %i12 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__begin_9 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i12, i32 0, i32 1
  %i13 = load %struct.User*, %struct.User** %__begin_9, align 8
  %i14 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %__v.addr, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %i14, i32 0, i32 0
  store %struct.User* %i13, %struct.User** %__first_, align 8
  %call10 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  call void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE14__annotate_newEm(%"class.std::__1::vector"* %this1, i64 %call10) #14
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this1)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %call = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEED2Ev(%"struct.std::__1::__split_buffer"* %this1) #14
  ret %"struct.std::__1::__split_buffer"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8max_sizeEv(%"class.std::__1::vector"* %this) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %ref.tmp = alloca i64, align 8
  %ref.tmp3 = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  %call2 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE8max_sizeERKS3_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call) #14
  store i64 %call2, i64* %ref.tmp, align 8
  %call4 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #14
  store i64 %call4, i64* %ref.tmp3, align 8
  %call5 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %ref.tmp3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i64, i64* %call5, align 8
  ret i64 %i1
}

; Function Attrs: noreturn
declare void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"*) #8

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call i64 @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::__vector_base"* %i) #14
  ret i64 %call
}

; Function Attrs: noinline optnone sspstrong uwtable
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

; Function Attrs: noinline optnone sspstrong uwtable
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

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE8max_sizeERKS3_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_max_size", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_max_size"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE10__max_sizeENS_17integral_constantIbLb1EEERKS3_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1) #14
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #1 align 2 {
entry:
  %call = call i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #14
  ret i64 %call
}

; Function Attrs: noinline optnone sspstrong uwtable
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
  br i1 %call, label %bb, label %bb4

cond.true:                                        ; preds = %bb
  %i2 = load i64*, i64** %__b.addr, align 8
  br label %cond.end

cond.false:                                       ; preds = %bb4
  %i3 = load i64*, i64** %__a.addr, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond-lvalue = phi i64* [ %i2, %cond.true ], [ %i3, %cond.false ]
  ret i64* %cond-lvalue

bb:                                               ; preds = %entry
  br label %cond.true

bb4:                                              ; preds = %entry
  br label %cond.false
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
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

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE10__max_sizeENS_17integral_constantIbLb1EEERKS3_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call i64 @_ZNKSt3__19allocatorI4UserE8max_sizeEv(%"class.std::__1::allocator"* %i1) #14
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorI4UserE8max_sizeEv(%"class.std::__1::allocator"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  ret i64 2305843009213693951
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem.0"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %i) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorI4UserEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.0"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.0"* %this, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.0"*, %"struct.std::__1::__compressed_pair_elem.0"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.0"* %this1 to %"class.std::__1::allocator"*
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__123__libcpp_numeric_limitsIlLb1EE3maxEv() #1 align 2 {
entry:
  ret i64 9223372036854775807
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this1) #14
  %i = load %struct.User*, %struct.User** %call, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.User* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.User* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base"*, align 8
  store %"class.std::__1::__vector_base"* %this, %"class.std::__1::__vector_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base"*, %"class.std::__1::__vector_base"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair"* %__end_cap_) #14
  ret %struct.User** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__117__compressed_pairIP4UserNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair"*, align 8
  store %"class.std::__1::__compressed_pair"* %this, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair"*, %"class.std::__1::__compressed_pair"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #14
  ret %struct.User** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem"*, align 8
  store %"struct.std::__1::__compressed_pair_elem"* %this, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem"*, %"struct.std::__1::__compressed_pair_elem"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem", %"struct.std::__1::__compressed_pair_elem"* %this1, i32 0, i32 0
  ret %struct.User** %__value_
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
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
  br i1 %call, label %bb, label %bb4

cond.true:                                        ; preds = %bb
  %i2 = load i64*, i64** %__b.addr, align 8
  br label %cond.end

cond.false:                                       ; preds = %bb4
  %i3 = load i64*, i64** %__a.addr, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond-lvalue = phi i64* [ %i2, %cond.true ], [ %i3, %cond.false ]
  ret i64* %cond-lvalue

bb:                                               ; preds = %entry
  br label %cond.true

bb4:                                              ; preds = %entry
  br label %cond.false
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEEC2EmmS4_(%"struct.std::__1::__split_buffer"* returned %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
entry:
  %retval = alloca %"struct.std::__1::__split_buffer"*, align 8
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
  store %"struct.std::__1::__split_buffer"* %this1, %"struct.std::__1::__split_buffer"** %retval, align 8
  %i = bitcast %"struct.std::__1::__split_buffer"* %this1 to %"class.std::__1::__split_buffer_common"*
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  store i8* null, i8** %ref.tmp, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.10"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEEC1IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.10"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load i64, i64* %__cap.addr, align 8
  %cmp = icmp ne i64 %i2, 0
  br i1 %cmp, label %bb, label %bb9

cond.true:                                        ; preds = %bb
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #14
  %i3 = load i64, i64* %__cap.addr, align 8
  %call3 = call %struct.User* @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE8allocateERS3_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2, i64 %i3)
  br label %cond.end

cond.false:                                       ; preds = %bb9
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi %struct.User* [ %call3, %cond.true ], [ null, %cond.false ]
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  store %struct.User* %cond, %struct.User** %__first_, align 8
  %__first_4 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i4 = load %struct.User*, %struct.User** %__first_4, align 8
  %i5 = load i64, i64* %__start.addr, align 8
  %add.ptr = getelementptr %struct.User, %struct.User* %i4, i64 %i5
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  store %struct.User* %add.ptr, %struct.User** %__end_, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 1
  store %struct.User* %add.ptr, %struct.User** %__begin_, align 8
  %__first_5 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i6 = load %struct.User*, %struct.User** %__first_5, align 8
  %i7 = load i64, i64* %__cap.addr, align 8
  %add.ptr6 = getelementptr %struct.User, %struct.User* %i6, i64 %i7
  %call7 = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #14
  store %struct.User* %add.ptr6, %struct.User** %call7, align 8
  %i8 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %retval, align 8
  ret %"struct.std::__1::__split_buffer"* %i8

bb:                                               ; preds = %entry
  br label %cond.true

bb9:                                              ; preds = %entry
  br label %cond.false
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.10"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEEC1IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.10"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.10"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.10"* %this, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.10"*, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.10"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEEC2IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.10"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  ret %"class.std::__1::__compressed_pair.10"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE8allocateERS3_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, i64 %__n) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call %struct.User* @_ZNSt3__19allocatorI4UserE8allocateEm(%"class.std::__1::allocator"* %i, i64 %i1)
  ret %struct.User* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.10"* %__end_cap_) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.10"* %__end_cap_) #14
  ret %struct.User** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.10"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEEC2IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.10"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.10"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::__compressed_pair.10"* %this, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator"* %__t2, %"class.std::__1::allocator"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.10"*, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.10"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #14
  %call2 = call %"struct.std::__1::__compressed_pair_elem"* @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.10"* %this1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.11"*
  %i5 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t2.addr, align 8
  %call3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorI4UserEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i5) #14
  %call4 = call %"struct.std::__1::__compressed_pair_elem.11"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4UserEELi1ELb0EEC2IS4_vEEOT_(%"struct.std::__1::__compressed_pair_elem.11"* %i4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call3)
  ret %"class.std::__1::__compressed_pair.10"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorI4UserEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"class.std::__1::allocator"* %__t, %"class.std::__1::allocator"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__t.addr, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__compressed_pair_elem.11"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4UserEELi1ELb0EEC2IS4_vEEOT_(%"struct.std::__1::__compressed_pair_elem.11"* returned %this, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.11"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.11"* %this, %"struct.std::__1::__compressed_pair_elem.11"** %this.addr, align 8
  store %"class.std::__1::allocator"* %__u, %"class.std::__1::allocator"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.11"*, %"struct.std::__1::__compressed_pair_elem.11"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.11", %"struct.std::__1::__compressed_pair_elem.11"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__17forwardIRNS_9allocatorI4UserEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i) #14
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__value_, align 8
  ret %"struct.std::__1::__compressed_pair_elem.11"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNSt3__19allocatorI4UserE8allocateEm(%"class.std::__1::allocator"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %cmp = icmp ugt i64 %i, 2305843009213693951
  br i1 %cmp, label %bb, label %bb3

if.then:                                          ; preds = %bb
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str.2, i64 0, i64 0)) #16
  unreachable

if.end:                                           ; preds = %bb3
  %i1 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i1, 8
  %call = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %mul, i64 4)
  %i2 = bitcast i8* %call to %struct.User*
  ret %struct.User* %i2

bb:                                               ; preds = %entry
  br label %if.then

bb3:                                              ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline noreturn optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__120__throw_length_errorEPKc(i8* %__msg) #9 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %__msg.addr = alloca i8*, align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store i8* %__msg, i8** %__msg.addr, align 8
  %exception = call i8* @__cxa_allocate_exception(i64 16) #14
  %i = bitcast i8* %exception to %"class.std::length_error"*
  %i1 = load i8*, i8** %__msg.addr, align 8
  %call = call %"class.std::length_error"* @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* %i, i8* %i1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  call void @__cxa_throw(i8* %exception, i8* bitcast (i8** @_ZTISt12length_error to i8*), i8* bitcast (%"class.std::length_error"* (%"class.std::length_error"*)* @_ZNSt12length_errorD1Ev to i8*)) #16
  unreachable
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %__size, i64 %__align) #0 {
entry:
  %retval = alloca i8*, align 8
  %__size.addr = alloca i64, align 8
  %__align.addr = alloca i64, align 8
  %__align_val = alloca i64, align 8
  store i64 %__size, i64* %__size.addr, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #14
  br i1 %call, label %bb, label %bb6

if.then:                                          ; preds = %bb
  %i1 = load i64, i64* %__align.addr, align 8
  store i64 %i1, i64* %__align_val, align 8
  %i2 = load i64, i64* %__size.addr, align 8
  %i3 = load i64, i64* %__align_val, align 8
  %call1 = call noalias nonnull i8* @_ZnwmSt11align_val_t(i64 %i2, i64 %i3) #13
  %mask = sub i64 %i3, 1
  %ptrint = ptrtoint i8* %call1 to i64
  %maskedptr = and i64 %ptrint, %mask
  %maskcond = icmp eq i64 %maskedptr, 0
  call void @llvm.assume(i1 %maskcond)
  store i8* %call1, i8** %retval, align 8
  br label %return

if.end:                                           ; preds = %bb6
  %i4 = load i64, i64* %__size.addr, align 8
  %call2 = call noalias nonnull i8* @_Znwm(i64 %i4) #13
  store i8* %call2, i8** %retval, align 8
  br label %return

return:                                           ; preds = %if.end, %if.then
  %i5 = load i8*, i8** %retval, align 8
  ret i8* %i5

bb:                                               ; preds = %entry
  br label %if.then

bb6:                                              ; preds = %entry
  br label %if.end
}

declare i8* @__cxa_allocate_exception(i64)

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::length_error"* @_ZNSt12length_errorC1EPKc(%"class.std::length_error"* returned %this, i8* %__s) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::length_error"*, align 8
  %__s.addr = alloca i8*, align 8
  store %"class.std::length_error"* %this, %"class.std::length_error"** %this.addr, align 8
  store i8* %__s, i8** %__s.addr, align 8
  %this1 = load %"class.std::length_error"*, %"class.std::length_error"** %this.addr, align 8
  %i = load i8*, i8** %__s.addr, align 8
  %call = call %"class.std::length_error"* @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* %this1, i8* %i)
  ret %"class.std::length_error"* %this1
}

declare void @__cxa_free_exception(i8*)

; Function Attrs: nounwind
declare %"class.std::length_error"* @_ZNSt12length_errorD1Ev(%"class.std::length_error"* returned) unnamed_addr #10

declare void @__cxa_throw(i8*, i8*, i8*)

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::length_error"* @_ZNSt12length_errorC2EPKc(%"class.std::length_error"* returned %this, i8* %__s) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::length_error"*, align 8
  %__s.addr = alloca i8*, align 8
  store %"class.std::length_error"* %this, %"class.std::length_error"** %this.addr, align 8
  store i8* %__s, i8** %__s.addr, align 8
  %this1 = load %"class.std::length_error"*, %"class.std::length_error"** %this.addr, align 8
  %i = bitcast %"class.std::length_error"* %this1 to %"class.std::logic_error"*
  %i1 = load i8*, i8** %__s.addr, align 8
  %call = call %"class.std::logic_error"* @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"* %i, i8* %i1)
  %i2 = bitcast %"class.std::length_error"* %this1 to i32 (...)***
  store i32 (...)** bitcast (i8** getelementptr inbounds ({ [5 x i8*] }, { [5 x i8*] }* @_ZTVSt12length_error, i32 0, inrange i32 0, i32 2) to i32 (...)**), i32 (...)*** %i2, align 8
  ret %"class.std::length_error"* %this1
}

declare %"class.std::logic_error"* @_ZNSt11logic_errorC2EPKc(%"class.std::logic_error"* returned, i8*) unnamed_addr #4

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %__align) #1 {
entry:
  %__align.addr = alloca i64, align 8
  store i64 %__align, i64* %__align.addr, align 8
  %i = load i64, i64* %__align.addr, align 8
  %cmp = icmp ugt i64 %i, 8
  ret i1 %cmp
}

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_ZnwmSt11align_val_t(i64, i64) #5

; Function Attrs: nounwind willreturn
declare void @llvm.assume(i1) #11

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.10"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.10"*, align 8
  store %"class.std::__1::__compressed_pair.10"* %this, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.10"*, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.10"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i, i64 8
  %i1 = bitcast i8* %add.ptr to %"struct.std::__1::__compressed_pair_elem.11"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4UserEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.11"* %i1) #14
  ret %"class.std::__1::allocator"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4UserEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.11"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.11"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.11"* %this, %"struct.std::__1::__compressed_pair_elem.11"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.11"*, %"struct.std::__1::__compressed_pair_elem.11"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.11", %"struct.std::__1::__compressed_pair_elem.11"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__value_, align 8
  ret %"class.std::__1::allocator"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.10"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.10"*, align 8
  store %"class.std::__1::__compressed_pair.10"* %this, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.10"*, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.10"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #14
  ret %struct.User** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE17__annotate_deleteEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %i = bitcast %struct.User* %call to i8*
  %call2 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %call3 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this1) #14
  %add.ptr = getelementptr %struct.User, %struct.User* %call2, i64 %call3
  %i1 = bitcast %struct.User* %add.ptr to i8*
  %call4 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %call5 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  %add.ptr6 = getelementptr %struct.User, %struct.User* %call4, i64 %call5
  %i2 = bitcast %struct.User* %add.ptr6 to i8*
  %call7 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %call8 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this1) #14
  %add.ptr9 = getelementptr %struct.User, %struct.User* %call7, i64 %call8
  %i3 = bitcast %struct.User* %add.ptr9 to i8*
  call void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i3) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE46__construct_backward_with_exception_guaranteesIS2_EENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS3_PT_S9_EE5valuesr31is_trivially_move_constructibleIS9_EE5valueEvE4typeERS3_SA_SA_RSA_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %arg, %struct.User* %__begin1, %struct.User* %__end1, %struct.User** nonnull align 8 dereferenceable(8) %__end2) #1 align 2 {
entry:
  %.addr = alloca %"class.std::__1::allocator"*, align 8
  %__begin1.addr = alloca %struct.User*, align 8
  %__end1.addr = alloca %struct.User*, align 8
  %__end2.addr = alloca %struct.User**, align 8
  %_Np = alloca i64, align 8
  store %"class.std::__1::allocator"* %arg, %"class.std::__1::allocator"** %.addr, align 8
  store %struct.User* %__begin1, %struct.User** %__begin1.addr, align 8
  store %struct.User* %__end1, %struct.User** %__end1.addr, align 8
  store %struct.User** %__end2, %struct.User*** %__end2.addr, align 8
  %i = load %struct.User*, %struct.User** %__end1.addr, align 8
  %i1 = load %struct.User*, %struct.User** %__begin1.addr, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.User* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.User* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  store i64 %sub.ptr.div, i64* %_Np, align 8
  %i2 = load i64, i64* %_Np, align 8
  %i3 = load %struct.User**, %struct.User*** %__end2.addr, align 8
  %i4 = load %struct.User*, %struct.User** %i3, align 8
  %idx.neg = sub i64 0, %i2
  %add.ptr = getelementptr %struct.User, %struct.User* %i4, i64 %idx.neg
  store %struct.User* %add.ptr, %struct.User** %i3, align 8
  %i5 = load i64, i64* %_Np, align 8
  %cmp = icmp sgt i64 %i5, 0
  br i1 %cmp, label %bb, label %bb12

if.then:                                          ; preds = %bb
  %i6 = load %struct.User**, %struct.User*** %__end2.addr, align 8
  %i7 = load %struct.User*, %struct.User** %i6, align 8
  %i8 = bitcast %struct.User* %i7 to i8*
  %i9 = load %struct.User*, %struct.User** %__begin1.addr, align 8
  %i10 = bitcast %struct.User* %i9 to i8*
  %i11 = load i64, i64* %_Np, align 8
  %mul = mul i64 %i11, 8
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i8, i8* align 4 %i10, i64 %mul, i1 false)
  br label %if.end

if.end:                                           ; preds = %bb12, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb12:                                             ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIP4UserEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.User** nonnull align 8 dereferenceable(8) %__x, %struct.User** nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca %struct.User**, align 8
  %__y.addr = alloca %struct.User**, align 8
  %__t = alloca %struct.User*, align 8
  store %struct.User** %__x, %struct.User*** %__x.addr, align 8
  store %struct.User** %__y, %struct.User*** %__y.addr, align 8
  %i = load %struct.User**, %struct.User*** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__14moveIRP4UserEEONS_16remove_referenceIT_E4typeEOS5_(%struct.User** nonnull align 8 dereferenceable(8) %i) #14
  %i1 = load %struct.User*, %struct.User** %call, align 8
  store %struct.User* %i1, %struct.User** %__t, align 8
  %i2 = load %struct.User**, %struct.User*** %__y.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__14moveIRP4UserEEONS_16remove_referenceIT_E4typeEOS5_(%struct.User** nonnull align 8 dereferenceable(8) %i2) #14
  %i3 = load %struct.User*, %struct.User** %call1, align 8
  %i4 = load %struct.User**, %struct.User*** %__x.addr, align 8
  store %struct.User* %i3, %struct.User** %i4, align 8
  %call2 = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__14moveIRP4UserEEONS_16remove_referenceIT_E4typeEOS5_(%struct.User** nonnull align 8 dereferenceable(8) %__t) #14
  %i5 = load %struct.User*, %struct.User** %call2, align 8
  %i6 = load %struct.User**, %struct.User*** %__y.addr, align 8
  store %struct.User* %i5, %struct.User** %i6, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE14__annotate_newEm(%"class.std::__1::vector"* %this, i64 %__current_size) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__current_size.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__current_size, i64* %__current_size.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %i = bitcast %struct.User* %call to i8*
  %call2 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %call3 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this1) #14
  %add.ptr = getelementptr %struct.User, %struct.User* %call2, i64 %call3
  %i1 = bitcast %struct.User* %add.ptr to i8*
  %call4 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %call5 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector"* %this1) #14
  %add.ptr6 = getelementptr %struct.User, %struct.User* %call4, i64 %call5
  %i2 = bitcast %struct.User* %add.ptr6 to i8*
  %call7 = call %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this1) #14
  %i3 = load i64, i64* %__current_size.addr, align 8
  %add.ptr8 = getelementptr %struct.User, %struct.User* %call7, i64 %i3
  %i4 = bitcast %struct.User* %add.ptr8 to i8*
  call void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i4) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector"* %this, i8* %arg, i8* %arg1, i8* %arg2, i8* %arg3) #1 align 2 {
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

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.User* @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__begin_, align 8
  %call = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %i1) #14
  ret %struct.User* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNSt3__14moveIRP4UserEEONS_16remove_referenceIT_E4typeEOS5_(%struct.User** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.User**, align 8
  store %struct.User** %__t, %struct.User*** %__t.addr, align 8
  %i = load %struct.User**, %struct.User*** %__t.addr, align 8
  ret %struct.User** %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEED2Ev(%"struct.std::__1::__split_buffer"* returned %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %retval = alloca %"struct.std::__1::__split_buffer"*, align 8
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer"* %this1, %"struct.std::__1::__split_buffer"** %retval, align 8
  call void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE5clearEv(%"struct.std::__1::__split_buffer"* %this1) #14
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__first_, align 8
  %tobool = icmp ne %struct.User* %i, null
  br i1 %tobool, label %bb, label %bb3

if.then:                                          ; preds = %bb
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #14
  %__first_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__first_2, align 8
  %call3 = call i64 @_ZNKSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE8capacityEv(%"struct.std::__1::__split_buffer"* %this1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE10deallocateERS3_PS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, %struct.User* %i1, i64 %call3) #14
  br label %if.end

if.end:                                           ; preds = %bb3, %invoke.cont
  %i2 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %retval, align 8
  ret %"struct.std::__1::__split_buffer"* %i2

bb:                                               ; preds = %entry
  br label %if.then

bb3:                                              ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE5clearEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 1
  %i = load %struct.User*, %struct.User** %__begin_, align 8
  call void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_(%"struct.std::__1::__split_buffer"* %this1, %struct.User* %i) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE10deallocateERS3_PS2_m(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p, i64 %__n) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i1 = load %struct.User*, %struct.User** %__p.addr, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__19allocatorI4UserE10deallocateEPS1_m(%"class.std::__1::allocator"* %i, %struct.User* %i1, i64 %i2) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE8capacityEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this1) #14
  %i = load %struct.User*, %struct.User** %call, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %__first_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.User* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.User* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_(%"struct.std::__1::__split_buffer"* %this, %struct.User* %__new_last) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__new_last.addr = alloca %struct.User*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.12", align 1
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store %struct.User* %__new_last, %struct.User** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__new_last.addr, align 8
  call void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this1, %struct.User* %i) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer"* %this, %struct.User* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %i = alloca %"struct.std::__1::integral_constant.12", align 1
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  %__new_last.addr = alloca %struct.User*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  store %struct.User* %__new_last, %struct.User** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load %struct.User*, %struct.User** %__new_last.addr, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  %i2 = load %struct.User*, %struct.User** %__end_, align 8
  %cmp = icmp ne %struct.User* %i1, %i2
  br i1 %cmp, label %bb, label %bb4

while.body:                                       ; preds = %bb
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer"* %this1) #14
  %__end_2 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 2
  %i3 = load %struct.User*, %struct.User** %__end_2, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i3, i32 -1
  store %struct.User* %incdec.ptr, %struct.User** %__end_2, align 8
  %call3 = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %incdec.ptr) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE7destroyIS2_EEvRS3_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call, %struct.User* %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %bb4
  ret void

bb:                                               ; preds = %while.cond
  br label %while.body

bb4:                                              ; preds = %while.cond
  br label %while.end
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE7destroyIS2_EEvRS3_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_destroy", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  %i = bitcast %"struct.std::__1::__has_destroy"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9__destroyIS2_EEvNS_17integral_constantIbLb1EEERS3_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, %struct.User* %i2)
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9__destroyIS2_EEvNS_17integral_constantIbLb1EEERS3_PT_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  call void @_ZNSt3__19allocatorI4UserE7destroyEPS1_(%"class.std::__1::allocator"* %i1, %struct.User* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorI4UserE7destroyEPS1_(%"class.std::__1::allocator"* %this, %struct.User* %__p) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorI4UserE10deallocateEPS1_m(%"class.std::__1::allocator"* %this, %struct.User* %__p, i64 %__n) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  %i1 = bitcast %struct.User* %i to i8*
  %i2 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i2, 8
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %i1, i64 %mul, i64 4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
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

; Function Attrs: noinline optnone sspstrong uwtable
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
  %call = call zeroext i1 @_ZNSt3__124__is_overaligned_for_newEm(i64 %i) #14
  br i1 %call, label %bb, label %bb7

if.then:                                          ; preds = %bb
  %i1 = load i64, i64* %__align.addr, align 8
  store i64 %i1, i64* %__align_val, align 8
  %i2 = load i8*, i8** %__ptr.addr, align 8
  %i3 = load i64, i64* %__size.addr, align 8
  %i4 = load i64, i64* %__align_val, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvmSt11align_val_t(i8* %i2, i64 %i3, i64 %i4)
  br label %return

if.else:                                          ; preds = %bb7
  %i5 = load i8*, i8** %__ptr.addr, align 8
  %i6 = load i64, i64* %__size.addr, align 8
  call void @_ZNSt3__117_DeallocateCaller27__do_deallocate_handle_sizeEPvm(i8* %i5, i64 %i6)
  br label %return

return:                                           ; preds = %if.else, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb7:                                              ; preds = %entry
  br label %if.else
}

; Function Attrs: noinline optnone sspstrong uwtable
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

; Function Attrs: noinline optnone sspstrong uwtable
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

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callISt11align_val_tEEvPvT_(i8* %__ptr, i64 %__a1) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  %__a1.addr = alloca i64, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  store i64 %__a1, i64* %__a1.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  %i1 = load i64, i64* %__a1.addr, align 8
  call void @_ZdlPvSt11align_val_t(i8* %i, i64 %i1) #17
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPvSt11align_val_t(i8*, i64) #12

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__117_DeallocateCaller9__do_callEPv(i8* %__ptr) #1 align 2 {
entry:
  %__ptr.addr = alloca i8*, align 8
  store i8* %__ptr, i8** %__ptr.addr, align 8
  %i = load i8*, i8** %__ptr.addr, align 8
  call void @_ZdlPv(i8* %i) #17
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) #12

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer"*, align 8
  store %"struct.std::__1::__split_buffer"* %this, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer"*, %"struct.std::__1::__split_buffer"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.10"* %__end_cap_) #14
  ret %struct.User** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__117__compressed_pairIP4UserRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.10"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.10"*, align 8
  store %"class.std::__1::__compressed_pair.10"* %this, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.10"*, %"class.std::__1::__compressed_pair.10"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.10"* %this1 to %"struct.std::__1::__compressed_pair_elem"*
  %call = call nonnull align 8 dereferenceable(8) %struct.User** @_ZNKSt3__122__compressed_pair_elemIP4UserLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem"* %i) #14
  ret %struct.User** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE22__construct_one_at_endIJRKS1_EEEvDpOT_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__args.addr = alloca %struct.User*, align 8
  %__tx = alloca %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load %struct.User*, %struct.User** %__pos_, align 8
  %call3 = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %i1) #14
  %i2 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call4 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i2) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %call2, %struct.User* %call3, %struct.User* nonnull align 4 dereferenceable(8) %call4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_5 = getelementptr inbounds %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction", %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load %struct.User*, %struct.User** %__pos_5, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i3, i32 1
  store %struct.User* %incdec.ptr, %struct.User** %__pos_5, align 8
  %call6 = call %"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<User, std::__1::allocator<User>>::_ConstructTransaction"* %__tx) #14
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE21__push_back_slow_pathIRKS1_EEvOT_(%"class.std::__1::vector"* %this, %struct.User* nonnull align 4 dereferenceable(8) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  %__a = alloca %"class.std::__1::allocator"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator"* @_ZNSt3__113__vector_baseI4UserNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base"* %i) #14
  store %"class.std::__1::allocator"* %call, %"class.std::__1::allocator"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorI4UserNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector"* %this1) #14
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %call5 = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i3 = load %struct.User*, %struct.User** %__end_, align 8
  %call6 = call %struct.User* @_ZNSt3__112__to_addressI4UserEEPT_S3_(%struct.User* %i3) #14
  %i4 = load %struct.User*, %struct.User** %__x.addr, align 8
  %call7 = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i2, %struct.User* %call6, %struct.User* nonnull align 4 dereferenceable(8) %call7)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_8 = getelementptr inbounds %"struct.std::__1::__split_buffer", %"struct.std::__1::__split_buffer"* %__v, i32 0, i32 2
  %i5 = load %struct.User*, %struct.User** %__end_8, align 8
  %incdec.ptr = getelementptr %struct.User, %struct.User* %i5, i32 1
  store %struct.User* %incdec.ptr, %struct.User** %__end_8, align 8
  call void @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector"* %this1, %"struct.std::__1::__split_buffer"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont9

invoke.cont9:                                     ; preds = %invoke.cont
  %call10 = call %"struct.std::__1::__split_buffer"* @_ZNSt3__114__split_bufferI4UserRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer"* %__v) #14
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct.13", align 1
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct.13"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE11__constructIS2_JRKS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %i1, %struct.User* %i2, %struct.User* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.User*, align 8
  store %struct.User* %__t, %struct.User** %__t.addr, align 8
  %i = load %struct.User*, %struct.User** %__t.addr, align 8
  ret %struct.User* %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4UserEEE11__constructIS2_JRKS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator"* nonnull align 1 dereferenceable(1) %__a, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %__a, %"class.std::__1::allocator"** %__a.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %__a.addr, align 8
  %i2 = load %struct.User*, %struct.User** %__p.addr, align 8
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__19allocatorI4UserE9constructIS1_JRKS1_EEEvPT_DpOT0_(%"class.std::__1::allocator"* %i1, %struct.User* %i2, %struct.User* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__19allocatorI4UserE9constructIS1_JRKS1_EEEvPT_DpOT0_(%"class.std::__1::allocator"* %this, %struct.User* %__p, %struct.User* nonnull align 4 dereferenceable(8) %__args) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  %__args.addr = alloca %struct.User*, align 8
  store %"class.std::__1::allocator"* %this, %"class.std::__1::allocator"** %this.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  store %struct.User* %__args, %struct.User** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator"*, %"class.std::__1::allocator"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  %i1 = bitcast %struct.User* %i to i8*
  %i2 = bitcast i8* %i1 to %struct.User*
  %i3 = load %struct.User*, %struct.User** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.User* @_ZNSt3__17forwardIRK4UserEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.User* nonnull align 4 dereferenceable(8) %i3) #14
  %i4 = bitcast %struct.User* %i2 to i8*
  %i5 = bitcast %struct.User* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i4, i8* align 4 %i5, i64 8, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.list.1* @_ZN4listI4RoleEC1Ev(%struct.list.1* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.list.1*, align 8
  store %struct.list.1* %this, %struct.list.1** %this.addr, align 8
  %this1 = load %struct.list.1*, %struct.list.1** %this.addr, align 8
  %call = call %struct.list.1* @_ZN4listI4RoleEC2Ev(%struct.list.1* %this1) #14
  ret %struct.list.1* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.list.1* @_ZN4listI4RoleEC2Ev(%struct.list.1* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.list.1*, align 8
  store %struct.list.1* %this, %struct.list.1** %this.addr, align 8
  %this1 = load %struct.list.1*, %struct.list.1** %this.addr, align 8
  %contents = getelementptr inbounds %struct.list.1, %struct.list.1* %this1, i32 0, i32 0
  %call = call %"class.std::__1::vector.2"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEC1Ev(%"class.std::__1::vector.2"* %contents) #14
  ret %struct.list.1* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::vector.2"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEC1Ev(%"class.std::__1::vector.2"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call %"class.std::__1::vector.2"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::vector.2"* %this1) #14
  ret %"class.std::__1::vector.2"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::vector.2"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::vector.2"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call %"class.std::__1::__vector_base.3"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::__vector_base.3"* %i) #14
  ret %"class.std::__1::vector.2"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__vector_base.3"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEEC2Ev(%"class.std::__1::__vector_base.3"* returned %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  %ref.tmp = alloca i8*, align 8
  %ref.tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__vector_base.3"* %this1 to %"class.std::__1::__vector_base_common"*
  %call = call %"class.std::__1::__vector_base_common"* @_ZNSt3__120__vector_base_commonILb1EEC2Ev(%"class.std::__1::__vector_base_common"* %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 0
  store %struct.Role* null, %struct.Role** %__begin_, align 8
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 1
  store %struct.Role* null, %struct.Role** %__end_, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 2
  store i8* null, i8** %ref.tmp, align 8
  %call4 = call %"class.std::__1::__compressed_pair.4"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  br label %invoke.cont3

invoke.cont3:                                     ; preds = %invoke.cont
  ret %"class.std::__1::__vector_base.3"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.4"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEEC1IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.4"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.4"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.4"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1)
  ret %"class.std::__1::__compressed_pair.4"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.4"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEEC2IDnNS_18__default_init_tagEEEOT_OT0_(%"class.std::__1::__compressed_pair.4"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %agg.tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #14
  %call2 = call %"struct.std::__1::__compressed_pair_elem.5"* @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.5"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.6"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call3 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #14
  %call4 = call %"struct.std::__1::__compressed_pair_elem.6"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.6"* %i2)
  ret %"class.std::__1::__compressed_pair.4"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__compressed_pair_elem.5"* @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.5"* returned %this, i8** nonnull align 8 dereferenceable(8) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  %__u.addr = alloca i8**, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  store i8** %__u, i8*** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.5"* %this1, i32 0, i32 0
  %i = load i8**, i8*** %__u.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i) #14
  store %struct.Role* null, %struct.Role** %__value_, align 8
  ret %"struct.std::__1::__compressed_pair_elem.5"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__compressed_pair_elem.6"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.6"* returned %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.6"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.6"* %this, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.6"*, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.6"* %this1 to %"class.std::__1::allocator.7"*
  %call = call %"class.std::__1::allocator.7"* @_ZNSt3__19allocatorI4RoleEC2Ev(%"class.std::__1::allocator.7"* %i1) #14
  ret %"struct.std::__1::__compressed_pair_elem.6"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::allocator.7"* @_ZNSt3__19allocatorI4RoleEC2Ev(%"class.std::__1::allocator.7"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  ret %"class.std::__1::allocator.7"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE9push_backEOS1_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__x.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__x, %struct.Role** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i, i32 0, i32 1
  %i1 = load %struct.Role*, %struct.Role** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %i2) #14
  %i3 = load %struct.Role*, %struct.Role** %call, align 8
  %cmp = icmp ult %struct.Role* %i1, %i3
  br i1 %cmp, label %bb, label %bb6

if.then:                                          ; preds = %bb
  %i4 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  %call2 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__14moveIR4RoleEEONS_16remove_referenceIT_E4typeEOS4_(%struct.Role* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE22__construct_one_at_endIJS1_EEEvDpOT_(%"class.std::__1::vector.2"* %this1, %struct.Role* nonnull align 4 dereferenceable(8) %call2)
  br label %if.end

if.else:                                          ; preds = %bb6
  %i5 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  %call3 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__14moveIR4RoleEEONS_16remove_referenceIT_E4typeEOS4_(%struct.Role* nonnull align 4 dereferenceable(8) %i5) #14
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21__push_back_slow_pathIS1_EEvOT_(%"class.std::__1::vector.2"* %this1, %struct.Role* nonnull align 4 dereferenceable(8) %call3)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb6:                                              ; preds = %entry
  br label %if.else
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE9push_backERKS1_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__x) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__x.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__x, %struct.Role** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i, i32 0, i32 1
  %i1 = load %struct.Role*, %struct.Role** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %i2) #14
  %i3 = load %struct.Role*, %struct.Role** %call, align 8
  %cmp = icmp ne %struct.Role* %i1, %i3
  br i1 %cmp, label %bb, label %bb6

if.then:                                          ; preds = %bb
  %i4 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE22__construct_one_at_endIJRKS1_EEEvDpOT_(%"class.std::__1::vector.2"* %this1, %struct.Role* nonnull align 4 dereferenceable(8) %i4)
  br label %if.end

if.else:                                          ; preds = %bb6
  %i5 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21__push_back_slow_pathIRKS1_EEvOT_(%"class.std::__1::vector.2"* %this1, %struct.Role* nonnull align 4 dereferenceable(8) %i5)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb6:                                              ; preds = %entry
  br label %if.else
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE22__construct_one_at_endIJS1_EEEvDpOT_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  %__tx = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector.2"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load %struct.Role*, %struct.Role** %__pos_, align 8
  %call3 = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %i1) #14
  %i2 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call4 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i2) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call2, %struct.Role* %call3, %struct.Role* nonnull align 4 dereferenceable(8) %call4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_5 = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load %struct.Role*, %struct.Role** %__pos_5, align 8
  %incdec.ptr = getelementptr %struct.Role, %struct.Role* %i3, i32 1
  store %struct.Role* %incdec.ptr, %struct.Role** %__pos_5, align 8
  %call6 = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__14moveIR4RoleEEONS_16remove_referenceIT_E4typeEOS4_(%struct.Role* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.Role*, align 8
  store %struct.Role* %__t, %struct.Role** %__t.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__t.addr, align 8
  ret %struct.Role* %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21__push_back_slow_pathIS1_EEvOT_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__x.addr = alloca %struct.Role*, align 8
  %__a = alloca %"class.std::__1::allocator.7"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer.15", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__x, %struct.Role** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  store %"class.std::__1::allocator.7"* %call, %"class.std::__1::allocator.7"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector.2"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a, align 8
  %call5 = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer.15"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %__v, i32 0, i32 2
  %i3 = load %struct.Role*, %struct.Role** %__end_, align 8
  %call6 = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %i3) #14
  %i4 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  %call7 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i2, %struct.Role* %call6, %struct.Role* nonnull align 4 dereferenceable(8) %call7)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_8 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %__v, i32 0, i32 2
  %i5 = load %struct.Role*, %struct.Role** %__end_8, align 8
  %incdec.ptr = getelementptr %struct.Role, %struct.Role* %i5, i32 1
  store %struct.Role* %incdec.ptr, %struct.Role** %__end_8, align 8
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector.2"* %this1, %"struct.std::__1::__split_buffer.15"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont9

invoke.cont9:                                     ; preds = %invoke.cont
  %call10 = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer.15"* %__v) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.5"* %this1, i32 0, i32 0
  ret %struct.Role** %__value_
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* returned %this, %"class.std::__1::vector.2"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector.2"* %__v, %"class.std::__1::vector.2"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %i = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %__v.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionC2ERS4_m(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, %"class.std::__1::vector.2"* nonnull align 8 dereferenceable(24) %i, i64 %i1)
  ret %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct.14", align 1
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct.14"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE11__constructIS2_JS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1, %struct.Role* %i2, %struct.Role* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %__p) #1 {
entry:
  %__p.addr = alloca %struct.Role*, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__p.addr, align 8
  ret %struct.Role* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.Role*, align 8
  store %struct.Role* %__t, %struct.Role** %__t.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__t.addr, align 8
  ret %struct.Role* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1) #14
  ret %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionC2ERS4_m(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* returned %this, %"class.std::__1::vector.2"* nonnull align 8 dereferenceable(24) %__v, i64 %__n) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, align 8
  %__v.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__n.addr = alloca i64, align 8
  store %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  store %"class.std::__1::vector.2"* %__v, %"class.std::__1::vector.2"** %__v.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %__v.addr, align 8
  store %"class.std::__1::vector.2"* %i, %"class.std::__1::vector.2"** %__v_, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %__v.addr, align 8
  %i2 = bitcast %"class.std::__1::vector.2"* %i1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i2, i32 0, i32 1
  %i3 = load %struct.Role*, %struct.Role** %__end_, align 8
  store %struct.Role* %i3, %struct.Role** %__pos_, align 8
  %__new_end_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, i32 0, i32 2
  %i4 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %__v.addr, align 8
  %i5 = bitcast %"class.std::__1::vector.2"* %i4 to %"class.std::__1::__vector_base.3"*
  %__end_2 = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i5, i32 0, i32 1
  %i6 = load %struct.Role*, %struct.Role** %__end_2, align 8
  %i7 = load i64, i64* %__n.addr, align 8
  %add.ptr = getelementptr %struct.Role, %struct.Role* %i6, i64 %i7
  store %struct.Role* %add.ptr, %struct.Role** %__new_end_, align 8
  ret %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE11__constructIS2_JS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__19allocatorI4RoleE9constructIS1_JS1_EEEvPT_DpOT0_(%"class.std::__1::allocator.7"* %i1, %struct.Role* %i2, %struct.Role* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__19allocatorI4RoleE9constructIS1_JS1_EEEvPT_DpOT0_(%"class.std::__1::allocator.7"* %this, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i1 = bitcast %struct.Role* %i to i8*
  %i2 = bitcast i8* %i1 to %struct.Role*
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardI4RoleEEOT_RNS_16remove_referenceIS2_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  %i4 = bitcast %struct.Role* %i2 to i8*
  %i5 = bitcast %struct.Role* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i4, i8* align 4 %i5, i64 8, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.6"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.6"* %i) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.6"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.6"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.6"* %this, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.6"*, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.6"* %this1 to %"class.std::__1::allocator.7"*
  ret %"class.std::__1::allocator.7"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionD2Ev(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, align 8
  store %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %this1 = load %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"*, %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"** %this.addr, align 8
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, i32 0, i32 1
  %i = load %struct.Role*, %struct.Role** %__pos_, align 8
  %__v_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %__v_, align 8
  %i2 = bitcast %"class.std::__1::vector.2"* %i1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i2, i32 0, i32 1
  store %struct.Role* %i, %struct.Role** %__end_, align 8
  ret %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector.2"* %this, i64 %__new_size) #0 align 2 {
entry:
  %retval = alloca i64, align 8
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__new_size.addr = alloca i64, align 8
  %__ms = alloca i64, align 8
  %__cap = alloca i64, align 8
  %ref.tmp = alloca i64, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store i64 %__new_size, i64* %__new_size.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8max_sizeEv(%"class.std::__1::vector.2"* %this1) #14
  store i64 %call, i64* %__ms, align 8
  %i = load i64, i64* %__new_size.addr, align 8
  %i1 = load i64, i64* %__ms, align 8
  %cmp = icmp ugt i64 %i, %i1
  br i1 %cmp, label %bb, label %bb9

if.then:                                          ; preds = %bb
  %i2 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base_common"*
  call void @_ZNKSt3__120__vector_base_commonILb1EE20__throw_length_errorEv(%"class.std::__1::__vector_base_common"* %i2) #16
  unreachable

if.end:                                           ; preds = %bb9
  %call2 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this1) #14
  store i64 %call2, i64* %__cap, align 8
  %i3 = load i64, i64* %__cap, align 8
  %i4 = load i64, i64* %__ms, align 8
  %div = udiv i64 %i4, 2
  %cmp3 = icmp uge i64 %i3, %div
  br i1 %cmp3, label %bb10, label %bb11

if.then4:                                         ; preds = %bb10
  %i5 = load i64, i64* %__ms, align 8
  store i64 %i5, i64* %retval, align 8
  br label %return

if.end5:                                          ; preds = %bb11
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

bb:                                               ; preds = %entry
  br label %if.then

bb9:                                              ; preds = %entry
  br label %if.end

bb10:                                             ; preds = %if.end
  br label %if.then4

bb11:                                             ; preds = %if.end
  br label %if.end5
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer.15"* returned %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %i = load i64, i64* %__cap.addr, align 8
  %i1 = load i64, i64* %__start.addr, align 8
  %i2 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %call = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEEC2EmmS4_(%"struct.std::__1::__split_buffer.15"* %this1, i64 %i, i64 %i1, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i2)
  ret %"struct.std::__1::__split_buffer.15"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector.2"* %this, %"struct.std::__1::__split_buffer.15"* nonnull align 8 dereferenceable(40) %__v) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__v.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer.15"* %__v, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  call void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE17__annotate_deleteEv(%"class.std::__1::vector.2"* %this1) #14
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  %i1 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i1, i32 0, i32 0
  %i2 = load %struct.Role*, %struct.Role** %__begin_, align 8
  %i3 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i3, i32 0, i32 1
  %i4 = load %struct.Role*, %struct.Role** %__end_, align 8
  %i5 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %__begin_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %i5, i32 0, i32 1
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE46__construct_backward_with_exception_guaranteesIS2_EENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS3_PT_S9_EE5valuesr31is_trivially_move_constructibleIS9_EE5valueEvE4typeERS3_SA_SA_RSA_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call, %struct.Role* %i2, %struct.Role* %i4, %struct.Role** nonnull align 8 dereferenceable(8) %__begin_2)
  %i6 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__begin_3 = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i6, i32 0, i32 0
  %i7 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %__begin_4 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %i7, i32 0, i32 1
  call void @_ZNSt3__14swapIP4RoleEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.Role** nonnull align 8 dereferenceable(8) %__begin_3, %struct.Role** nonnull align 8 dereferenceable(8) %__begin_4) #14
  %i8 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__end_5 = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i8, i32 0, i32 1
  %i9 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %__end_6 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %i9, i32 0, i32 2
  call void @_ZNSt3__14swapIP4RoleEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.Role** nonnull align 8 dereferenceable(8) %__end_5, %struct.Role** nonnull align 8 dereferenceable(8) %__end_6) #14
  %i10 = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call7 = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %i10) #14
  %i11 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %call8 = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer.15"* %i11) #14
  call void @_ZNSt3__14swapIP4RoleEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.Role** nonnull align 8 dereferenceable(8) %call7, %struct.Role** nonnull align 8 dereferenceable(8) %call8) #14
  %i12 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %__begin_9 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %i12, i32 0, i32 1
  %i13 = load %struct.Role*, %struct.Role** %__begin_9, align 8
  %i14 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %__v.addr, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %i14, i32 0, i32 0
  store %struct.Role* %i13, %struct.Role** %__first_, align 8
  %call10 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  call void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE14__annotate_newEm(%"class.std::__1::vector.2"* %this1, i64 %call10) #14
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector.2"* %this1)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer.15"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %call = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEED2Ev(%"struct.std::__1::__split_buffer.15"* %this1) #14
  ret %"struct.std::__1::__split_buffer.15"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8max_sizeEv(%"class.std::__1::vector.2"* %this) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %ref.tmp = alloca i64, align 8
  %ref.tmp3 = alloca i64, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  %call2 = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE8max_sizeERKS3_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call) #14
  store i64 %call2, i64* %ref.tmp, align 8
  %call4 = call i64 @_ZNSt3__114numeric_limitsIlE3maxEv() #14
  store i64 %call4, i64* %ref.tmp3, align 8
  %call5 = call nonnull align 8 dereferenceable(8) i64* @_ZNSt3__13minImEERKT_S3_S3_(i64* nonnull align 8 dereferenceable(8) %ref.tmp, i64* nonnull align 8 dereferenceable(8) %ref.tmp3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i64, i64* %call5, align 8
  ret i64 %i1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call i64 @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::__vector_base.3"* %i) #14
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE8max_sizeERKS3_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_max_size.18", align 1
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i = bitcast %"struct.std::__1::__has_max_size.18"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %call = call i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE10__max_sizeENS_17integral_constantIbLb1EEERKS3_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1) #14
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 2
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE10__max_sizeENS_17integral_constantIbLb1EEERKS3_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a) #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %call = call i64 @_ZNKSt3__19allocatorI4RoleE8max_sizeEv(%"class.std::__1::allocator.7"* %i1) #14
  ret i64 %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__19allocatorI4RoleE8max_sizeEv(%"class.std::__1::allocator.7"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  ret i64 2305843009213693951
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.6"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.6"* %i) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNKSt3__122__compressed_pair_elemINS_9allocatorI4RoleEELi1ELb1EE5__getEv(%"struct.std::__1::__compressed_pair_elem.6"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.6"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.6"* %this, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.6"*, %"struct.std::__1::__compressed_pair_elem.6"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__compressed_pair_elem.6"* %this1 to %"class.std::__1::allocator.7"*
  ret %"class.std::__1::allocator.7"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::__vector_base.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %this1) #14
  %i = load %struct.Role*, %struct.Role** %call, align 8
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 0
  %i1 = load %struct.Role*, %struct.Role** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.Role* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.Role* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE9__end_capEv(%"class.std::__1::__vector_base.3"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__vector_base.3"*, align 8
  store %"class.std::__1::__vector_base.3"* %this, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %this1 = load %"class.std::__1::__vector_base.3"*, %"class.std::__1::__vector_base.3"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %this1, i32 0, i32 2
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.4"* %__end_cap_) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__117__compressed_pairIP4RoleNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.4"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.4"*, align 8
  store %"class.std::__1::__compressed_pair.4"* %this, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.4"*, %"class.std::__1::__compressed_pair.4"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.4"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.5"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.5"* %this, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.5"*, %"struct.std::__1::__compressed_pair_elem.5"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.5", %"struct.std::__1::__compressed_pair_elem.5"* %this1, i32 0, i32 0
  ret %struct.Role** %__value_
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEEC2EmmS4_(%"struct.std::__1::__split_buffer.15"* returned %this, i64 %__cap, i64 %__start, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a) unnamed_addr #0 align 2 {
entry:
  %retval = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %__cap.addr = alloca i64, align 8
  %__start.addr = alloca i64, align 8
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %ref.tmp = alloca i8*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store i64 %__cap, i64* %__cap.addr, align 8
  store i64 %__start, i64* %__start.addr, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer.15"* %this1, %"struct.std::__1::__split_buffer.15"** %retval, align 8
  %i = bitcast %"struct.std::__1::__split_buffer.15"* %this1 to %"class.std::__1::__split_buffer_common"*
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 3
  store i8* null, i8** %ref.tmp, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.16"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEEC1IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.16"* %__end_cap_, i8** nonnull align 8 dereferenceable(8) %ref.tmp, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load i64, i64* %__cap.addr, align 8
  %cmp = icmp ne i64 %i2, 0
  br i1 %cmp, label %bb, label %bb9

cond.true:                                        ; preds = %bb
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  %i3 = load i64, i64* %__cap.addr, align 8
  %call3 = call %struct.Role* @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE8allocateERS3_m(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call2, i64 %i3)
  br label %cond.end

cond.false:                                       ; preds = %bb9
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi %struct.Role* [ %call3, %cond.true ], [ null, %cond.false ]
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  store %struct.Role* %cond, %struct.Role** %__first_, align 8
  %__first_4 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  %i4 = load %struct.Role*, %struct.Role** %__first_4, align 8
  %i5 = load i64, i64* %__start.addr, align 8
  %add.ptr = getelementptr %struct.Role, %struct.Role* %i4, i64 %i5
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 2
  store %struct.Role* %add.ptr, %struct.Role** %__end_, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 1
  store %struct.Role* %add.ptr, %struct.Role** %__begin_, align 8
  %__first_5 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  %i6 = load %struct.Role*, %struct.Role** %__first_5, align 8
  %i7 = load i64, i64* %__cap.addr, align 8
  %add.ptr6 = getelementptr %struct.Role, %struct.Role* %i6, i64 %i7
  %call7 = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  store %struct.Role* %add.ptr6, %struct.Role** %call7, align 8
  %i8 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %retval, align 8
  ret %"struct.std::__1::__split_buffer.15"* %i8

bb:                                               ; preds = %entry
  br label %cond.true

bb9:                                              ; preds = %entry
  br label %cond.false
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.16"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEEC1IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.16"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.16"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::__compressed_pair.16"* %this, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator.7"* %__t2, %"class.std::__1::allocator.7"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.16"*, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %i = load i8**, i8*** %__t1.addr, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__t2.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.16"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEEC2IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.16"* %this1, i8** nonnull align 8 dereferenceable(8) %i, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1)
  ret %"class.std::__1::__compressed_pair.16"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %struct.Role* @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE8allocateERS3_m(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, i64 %__n) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %call = call %struct.Role* @_ZNSt3__19allocatorI4RoleE8allocateEm(%"class.std::__1::allocator.7"* %i, i64 %i1)
  ret %struct.Role* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 3
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.16"* %__end_cap_) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.16"* %__end_cap_) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.16"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEEC2IDnS5_EEOT_OT0_(%"class.std::__1::__compressed_pair.16"* returned %this, i8** nonnull align 8 dereferenceable(8) %__t1, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.16"*, align 8
  %__t1.addr = alloca i8**, align 8
  %__t2.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::__compressed_pair.16"* %this, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  store i8** %__t1, i8*** %__t1.addr, align 8
  store %"class.std::__1::allocator.7"* %__t2, %"class.std::__1::allocator.7"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.16"*, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.16"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %i1 = load i8**, i8*** %__t1.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) i8** @_ZNSt3__17forwardIDnEEOT_RNS_16remove_referenceIS1_E4typeE(i8** nonnull align 8 dereferenceable(8) %i1) #14
  %call2 = call %"struct.std::__1::__compressed_pair_elem.5"* @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EEC2IDnvEEOT_(%"struct.std::__1::__compressed_pair_elem.5"* %i, i8** nonnull align 8 dereferenceable(8) %call)
  %i2 = bitcast %"class.std::__1::__compressed_pair.16"* %this1 to i8*
  %i3 = getelementptr inbounds i8, i8* %i2, i64 8
  %i4 = bitcast i8* %i3 to %"struct.std::__1::__compressed_pair_elem.17"*
  %i5 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__t2.addr, align 8
  %call3 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__17forwardIRNS_9allocatorI4RoleEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i5) #14
  %call4 = call %"struct.std::__1::__compressed_pair_elem.17"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4RoleEELi1ELb0EEC2IS4_vEEOT_(%"struct.std::__1::__compressed_pair_elem.17"* %i4, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call3)
  ret %"class.std::__1::__compressed_pair.16"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__17forwardIRNS_9allocatorI4RoleEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"class.std::__1::allocator.7"* %__t, %"class.std::__1::allocator.7"** %__t.addr, align 8
  %i = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__t.addr, align 8
  ret %"class.std::__1::allocator.7"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__compressed_pair_elem.17"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4RoleEELi1ELb0EEC2IS4_vEEOT_(%"struct.std::__1::__compressed_pair_elem.17"* returned %this, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__u) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.17"*, align 8
  %__u.addr = alloca %"class.std::__1::allocator.7"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.17"* %this, %"struct.std::__1::__compressed_pair_elem.17"** %this.addr, align 8
  store %"class.std::__1::allocator.7"* %__u, %"class.std::__1::allocator.7"** %__u.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.17"*, %"struct.std::__1::__compressed_pair_elem.17"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.17", %"struct.std::__1::__compressed_pair_elem.17"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__u.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__17forwardIRNS_9allocatorI4RoleEEEEOT_RNS_16remove_referenceIS5_E4typeE(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i) #14
  store %"class.std::__1::allocator.7"* %call, %"class.std::__1::allocator.7"** %__value_, align 8
  ret %"struct.std::__1::__compressed_pair_elem.17"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %struct.Role* @_ZNSt3__19allocatorI4RoleE8allocateEm(%"class.std::__1::allocator.7"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %cmp = icmp ugt i64 %i, 2305843009213693951
  br i1 %cmp, label %bb, label %bb3

if.then:                                          ; preds = %bb
  call void @_ZNSt3__120__throw_length_errorEPKc(i8* getelementptr inbounds ([68 x i8], [68 x i8]* @.str.2, i64 0, i64 0)) #16
  unreachable

if.end:                                           ; preds = %bb3
  %i1 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i1, 8
  %call = call i8* @_ZNSt3__117__libcpp_allocateEmm(i64 %mul, i64 4)
  %i2 = bitcast i8* %call to %struct.Role*
  ret %struct.Role* %i2

bb:                                               ; preds = %entry
  br label %if.then

bb3:                                              ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE6secondEv(%"class.std::__1::__compressed_pair.16"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.16"*, align 8
  store %"class.std::__1::__compressed_pair.16"* %this, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.16"*, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.16"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i, i64 8
  %i1 = bitcast i8* %add.ptr to %"struct.std::__1::__compressed_pair_elem.17"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4RoleEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.17"* %i1) #14
  ret %"class.std::__1::allocator.7"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__122__compressed_pair_elemIRNS_9allocatorI4RoleEELi1ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.17"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.17"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.17"* %this, %"struct.std::__1::__compressed_pair_elem.17"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.17"*, %"struct.std::__1::__compressed_pair_elem.17"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.17", %"struct.std::__1::__compressed_pair_elem.17"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__value_, align 8
  ret %"class.std::__1::allocator.7"* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.16"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.16"*, align 8
  store %"class.std::__1::__compressed_pair.16"* %this, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.16"*, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.16"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE17__annotate_deleteEv(%"class.std::__1::vector.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %i = bitcast %struct.Role* %call to i8*
  %call2 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %call3 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this1) #14
  %add.ptr = getelementptr %struct.Role, %struct.Role* %call2, i64 %call3
  %i1 = bitcast %struct.Role* %add.ptr to i8*
  %call4 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %call5 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  %add.ptr6 = getelementptr %struct.Role, %struct.Role* %call4, i64 %call5
  %i2 = bitcast %struct.Role* %add.ptr6 to i8*
  %call7 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %call8 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this1) #14
  %add.ptr9 = getelementptr %struct.Role, %struct.Role* %call7, i64 %call8
  %i3 = bitcast %struct.Role* %add.ptr9 to i8*
  call void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector.2"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i3) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE46__construct_backward_with_exception_guaranteesIS2_EENS_9enable_ifIXaaooL_ZNS_17integral_constantIbLb1EE5valueEEntsr15__has_constructIS3_PT_S9_EE5valuesr31is_trivially_move_constructibleIS9_EE5valueEvE4typeERS3_SA_SA_RSA_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %arg, %struct.Role* %__begin1, %struct.Role* %__end1, %struct.Role** nonnull align 8 dereferenceable(8) %__end2) #1 align 2 {
entry:
  %.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__begin1.addr = alloca %struct.Role*, align 8
  %__end1.addr = alloca %struct.Role*, align 8
  %__end2.addr = alloca %struct.Role**, align 8
  %_Np = alloca i64, align 8
  store %"class.std::__1::allocator.7"* %arg, %"class.std::__1::allocator.7"** %.addr, align 8
  store %struct.Role* %__begin1, %struct.Role** %__begin1.addr, align 8
  store %struct.Role* %__end1, %struct.Role** %__end1.addr, align 8
  store %struct.Role** %__end2, %struct.Role*** %__end2.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__end1.addr, align 8
  %i1 = load %struct.Role*, %struct.Role** %__begin1.addr, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.Role* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.Role* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  store i64 %sub.ptr.div, i64* %_Np, align 8
  %i2 = load i64, i64* %_Np, align 8
  %i3 = load %struct.Role**, %struct.Role*** %__end2.addr, align 8
  %i4 = load %struct.Role*, %struct.Role** %i3, align 8
  %idx.neg = sub i64 0, %i2
  %add.ptr = getelementptr %struct.Role, %struct.Role* %i4, i64 %idx.neg
  store %struct.Role* %add.ptr, %struct.Role** %i3, align 8
  %i5 = load i64, i64* %_Np, align 8
  %cmp = icmp sgt i64 %i5, 0
  br i1 %cmp, label %bb, label %bb12

if.then:                                          ; preds = %bb
  %i6 = load %struct.Role**, %struct.Role*** %__end2.addr, align 8
  %i7 = load %struct.Role*, %struct.Role** %i6, align 8
  %i8 = bitcast %struct.Role* %i7 to i8*
  %i9 = load %struct.Role*, %struct.Role** %__begin1.addr, align 8
  %i10 = bitcast %struct.Role* %i9 to i8*
  %i11 = load i64, i64* %_Np, align 8
  %mul = mul i64 %i11, 8
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i8, i8* align 4 %i10, i64 %mul, i1 false)
  br label %if.end

if.end:                                           ; preds = %bb12, %if.then
  ret void

bb:                                               ; preds = %entry
  br label %if.then

bb12:                                             ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__14swapIP4RoleEENS_9enable_ifIXaasr21is_move_constructibleIT_EE5valuesr18is_move_assignableIS4_EE5valueEvE4typeERS4_S7_(%struct.Role** nonnull align 8 dereferenceable(8) %__x, %struct.Role** nonnull align 8 dereferenceable(8) %__y) #1 {
entry:
  %__x.addr = alloca %struct.Role**, align 8
  %__y.addr = alloca %struct.Role**, align 8
  %__t = alloca %struct.Role*, align 8
  store %struct.Role** %__x, %struct.Role*** %__x.addr, align 8
  store %struct.Role** %__y, %struct.Role*** %__y.addr, align 8
  %i = load %struct.Role**, %struct.Role*** %__x.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__14moveIRP4RoleEEONS_16remove_referenceIT_E4typeEOS5_(%struct.Role** nonnull align 8 dereferenceable(8) %i) #14
  %i1 = load %struct.Role*, %struct.Role** %call, align 8
  store %struct.Role* %i1, %struct.Role** %__t, align 8
  %i2 = load %struct.Role**, %struct.Role*** %__y.addr, align 8
  %call1 = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__14moveIRP4RoleEEONS_16remove_referenceIT_E4typeEOS5_(%struct.Role** nonnull align 8 dereferenceable(8) %i2) #14
  %i3 = load %struct.Role*, %struct.Role** %call1, align 8
  %i4 = load %struct.Role**, %struct.Role*** %__x.addr, align 8
  store %struct.Role* %i3, %struct.Role** %i4, align 8
  %call2 = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__14moveIRP4RoleEEONS_16remove_referenceIT_E4typeEOS5_(%struct.Role** nonnull align 8 dereferenceable(8) %__t) #14
  %i5 = load %struct.Role*, %struct.Role** %call2, align 8
  %i6 = load %struct.Role**, %struct.Role*** %__y.addr, align 8
  store %struct.Role* %i5, %struct.Role** %i6, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE14__annotate_newEm(%"class.std::__1::vector.2"* %this, i64 %__current_size) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__current_size.addr = alloca i64, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store i64 %__current_size, i64* %__current_size.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %i = bitcast %struct.Role* %call to i8*
  %call2 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %call3 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this1) #14
  %add.ptr = getelementptr %struct.Role, %struct.Role* %call2, i64 %call3
  %i1 = bitcast %struct.Role* %add.ptr to i8*
  %call4 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %call5 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE8capacityEv(%"class.std::__1::vector.2"* %this1) #14
  %add.ptr6 = getelementptr %struct.Role, %struct.Role* %call4, i64 %call5
  %i2 = bitcast %struct.Role* %add.ptr6 to i8*
  %call7 = call %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this1) #14
  %i3 = load i64, i64* %__current_size.addr, align 8
  %add.ptr8 = getelementptr %struct.Role, %struct.Role* %call7, i64 %i3
  %i4 = bitcast %struct.Role* %add.ptr8 to i8*
  call void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector.2"* %this1, i8* %i, i8* %i1, i8* %i2, i8* %i4) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE26__invalidate_all_iteratorsEv(%"class.std::__1::vector.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE31__annotate_contiguous_containerEPKvS6_S6_S6_(%"class.std::__1::vector.2"* %this, i8* %arg, i8* %arg1, i8* %arg2, i8* %arg3) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %.addr = alloca i8*, align 8
  %.addr1 = alloca i8*, align 8
  %.addr2 = alloca i8*, align 8
  %.addr3 = alloca i8*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store i8* %arg, i8** %.addr, align 8
  store i8* %arg1, i8** %.addr1, align 8
  store i8* %arg2, i8** %.addr2, align 8
  store i8* %arg3, i8** %.addr3, align 8
  %this4 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %struct.Role* @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4dataEv(%"class.std::__1::vector.2"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base.3", %"class.std::__1::__vector_base.3"* %i, i32 0, i32 0
  %i1 = load %struct.Role*, %struct.Role** %__begin_, align 8
  %call = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %i1) #14
  ret %struct.Role* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNSt3__14moveIRP4RoleEEONS_16remove_referenceIT_E4typeEOS5_(%struct.Role** nonnull align 8 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.Role**, align 8
  store %struct.Role** %__t, %struct.Role*** %__t.addr, align 8
  %i = load %struct.Role**, %struct.Role*** %__t.addr, align 8
  ret %struct.Role** %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEED2Ev(%"struct.std::__1::__split_buffer.15"* returned %this) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %retval = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store %"struct.std::__1::__split_buffer.15"* %this1, %"struct.std::__1::__split_buffer.15"** %retval, align 8
  call void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE5clearEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  %i = load %struct.Role*, %struct.Role** %__first_, align 8
  %tobool = icmp ne %struct.Role* %i, null
  br i1 %tobool, label %bb, label %bb3

if.then:                                          ; preds = %bb
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  %__first_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  %i1 = load %struct.Role*, %struct.Role** %__first_2, align 8
  %call3 = call i64 @_ZNKSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE8capacityEv(%"struct.std::__1::__split_buffer.15"* %this1)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE10deallocateERS3_PS2_m(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call, %struct.Role* %i1, i64 %call3) #14
  br label %if.end

if.end:                                           ; preds = %bb3, %invoke.cont
  %i2 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %retval, align 8
  ret %"struct.std::__1::__split_buffer.15"* %i2

bb:                                               ; preds = %entry
  br label %if.then

bb3:                                              ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE5clearEv(%"struct.std::__1::__split_buffer.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %__begin_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 1
  %i = load %struct.Role*, %struct.Role** %__begin_, align 8
  call void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_(%"struct.std::__1::__split_buffer.15"* %this1, %struct.Role* %i) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE10deallocateERS3_PS2_m(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p, i64 %__n) #1 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %i = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i1 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  call void @_ZNSt3__19allocatorI4RoleE10deallocateEPS1_m(%"class.std::__1::allocator.7"* %i, %struct.Role* %i1, i64 %i2) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE8capacityEv(%"struct.std::__1::__split_buffer.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  %i = load %struct.Role*, %struct.Role** %call, align 8
  %__first_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 0
  %i1 = load %struct.Role*, %struct.Role** %__first_, align 8
  %sub.ptr.lhs.cast = ptrtoint %struct.Role* %i to i64
  %sub.ptr.rhs.cast = ptrtoint %struct.Role* %i1 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 8
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_(%"struct.std::__1::__split_buffer.15"* %this, %struct.Role* %__new_last) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %__new_last.addr = alloca %struct.Role*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant.12", align 1
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store %struct.Role* %__new_last, %struct.Role** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__new_last.addr, align 8
  call void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer.15"* %this1, %struct.Role* %i) #14
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE17__destruct_at_endEPS1_NS_17integral_constantIbLb0EEE(%"struct.std::__1::__split_buffer.15"* %this, %struct.Role* %__new_last) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %i = alloca %"struct.std::__1::integral_constant.12", align 1
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  %__new_last.addr = alloca %struct.Role*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  store %struct.Role* %__new_last, %struct.Role** %__new_last.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  br label %while.cond

while.cond:                                       ; preds = %invoke.cont, %entry
  %i1 = load %struct.Role*, %struct.Role** %__new_last.addr, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 2
  %i2 = load %struct.Role*, %struct.Role** %__end_, align 8
  %cmp = icmp ne %struct.Role* %i1, %i2
  br i1 %cmp, label %bb, label %bb4

while.body:                                       ; preds = %bb
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE7__allocEv(%"struct.std::__1::__split_buffer.15"* %this1) #14
  %__end_2 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 2
  %i3 = load %struct.Role*, %struct.Role** %__end_2, align 8
  %incdec.ptr = getelementptr %struct.Role, %struct.Role* %i3, i32 -1
  store %struct.Role* %incdec.ptr, %struct.Role** %__end_2, align 8
  %call3 = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %incdec.ptr) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE7destroyIS2_EEvRS3_PT_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call, %struct.Role* %call3)
  br label %invoke.cont

invoke.cont:                                      ; preds = %while.body
  br label %while.cond

while.end:                                        ; preds = %bb4
  ret void

bb:                                               ; preds = %while.cond
  br label %while.body

bb4:                                              ; preds = %while.cond
  br label %while.end
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE7destroyIS2_EEvRS3_PT_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_destroy.19", align 1
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  %i = bitcast %"struct.std::__1::__has_destroy.19"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9__destroyIS2_EEvNS_17integral_constantIbLb1EEERS3_PT_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1, %struct.Role* %i2)
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9__destroyIS2_EEvNS_17integral_constantIbLb1EEERS3_PT_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  call void @_ZNSt3__19allocatorI4RoleE7destroyEPS1_(%"class.std::__1::allocator.7"* %i1, %struct.Role* %i2)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorI4RoleE7destroyEPS1_(%"class.std::__1::allocator.7"* %this, %struct.Role* %__p) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__p.addr, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19allocatorI4RoleE10deallocateEPS1_m(%"class.std::__1::allocator.7"* %this, %struct.Role* %__p, i64 %__n) #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i1 = bitcast %struct.Role* %i to i8*
  %i2 = load i64, i64* %__n.addr, align 8
  %mul = mul i64 %i2, 8
  call void @_ZNSt3__119__libcpp_deallocateEPvmm(i8* %i1, i64 %mul, i64 4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEE9__end_capEv(%"struct.std::__1::__split_buffer.15"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__split_buffer.15"*, align 8
  store %"struct.std::__1::__split_buffer.15"* %this, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__split_buffer.15"*, %"struct.std::__1::__split_buffer.15"** %this.addr, align 8
  %__end_cap_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %this1, i32 0, i32 3
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.16"* %__end_cap_) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__117__compressed_pairIP4RoleRNS_9allocatorIS1_EEE5firstEv(%"class.std::__1::__compressed_pair.16"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.16"*, align 8
  store %"class.std::__1::__compressed_pair.16"* %this, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.16"*, %"class.std::__1::__compressed_pair.16"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.16"* %this1 to %"struct.std::__1::__compressed_pair_elem.5"*
  %call = call nonnull align 8 dereferenceable(8) %struct.Role** @_ZNKSt3__122__compressed_pair_elemIP4RoleLi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.5"* %i) #14
  ret %struct.Role** %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE22__construct_one_at_endIJRKS1_EEEvDpOT_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  %__tx = alloca %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %call = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionC1ERS4_m(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, %"class.std::__1::vector.2"* nonnull align 8 dereferenceable(24) %this1, i64 1)
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call2 = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  %__pos_ = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i1 = load %struct.Role*, %struct.Role** %__pos_, align 8
  %call3 = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %i1) #14
  %i2 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call4 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i2) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %call2, %struct.Role* %call3, %struct.Role* nonnull align 4 dereferenceable(8) %call4)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__pos_5 = getelementptr inbounds %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction", %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx, i32 0, i32 1
  %i3 = load %struct.Role*, %struct.Role** %__pos_5, align 8
  %incdec.ptr = getelementptr %struct.Role, %struct.Role* %i3, i32 1
  store %struct.Role* %incdec.ptr, %struct.Role** %__pos_5, align 8
  %call6 = call %"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21_ConstructTransactionD1Ev(%"struct.std::__1::vector<Role, std::__1::allocator<Role>>::_ConstructTransaction"* %__tx) #14
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE21__push_back_slow_pathIRKS1_EEvOT_(%"class.std::__1::vector.2"* %this, %struct.Role* nonnull align 4 dereferenceable(8) %__x) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::vector.2"*, align 8
  %__x.addr = alloca %struct.Role*, align 8
  %__a = alloca %"class.std::__1::allocator.7"*, align 8
  %__v = alloca %"struct.std::__1::__split_buffer.15", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::vector.2"* %this, %"class.std::__1::vector.2"** %this.addr, align 8
  store %struct.Role* %__x, %struct.Role** %__x.addr, align 8
  %this1 = load %"class.std::__1::vector.2"*, %"class.std::__1::vector.2"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector.2"* %this1 to %"class.std::__1::__vector_base.3"*
  %call = call nonnull align 1 dereferenceable(1) %"class.std::__1::allocator.7"* @_ZNSt3__113__vector_baseI4RoleNS_9allocatorIS1_EEE7__allocEv(%"class.std::__1::__vector_base.3"* %i) #14
  store %"class.std::__1::allocator.7"* %call, %"class.std::__1::allocator.7"** %__a, align 8
  %call2 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  %add = add i64 %call2, 1
  %call3 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE11__recommendEm(%"class.std::__1::vector.2"* %this1, i64 %add)
  %call4 = call i64 @_ZNKSt3__16vectorI4RoleNS_9allocatorIS1_EEE4sizeEv(%"class.std::__1::vector.2"* %this1) #14
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a, align 8
  %call5 = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEEC1EmmS4_(%"struct.std::__1::__split_buffer.15"* %__v, i64 %call3, i64 %call4, %"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1)
  %i2 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a, align 8
  %__end_ = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %__v, i32 0, i32 2
  %i3 = load %struct.Role*, %struct.Role** %__end_, align 8
  %call6 = call %struct.Role* @_ZNSt3__112__to_addressI4RoleEEPT_S3_(%struct.Role* %i3) #14
  %i4 = load %struct.Role*, %struct.Role** %__x.addr, align 8
  %call7 = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i4) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i2, %struct.Role* %call6, %struct.Role* nonnull align 4 dereferenceable(8) %call7)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %__end_8 = getelementptr inbounds %"struct.std::__1::__split_buffer.15", %"struct.std::__1::__split_buffer.15"* %__v, i32 0, i32 2
  %i5 = load %struct.Role*, %struct.Role** %__end_8, align 8
  %incdec.ptr = getelementptr %struct.Role, %struct.Role* %i5, i32 1
  store %struct.Role* %incdec.ptr, %struct.Role** %__end_8, align 8
  call void @_ZNSt3__16vectorI4RoleNS_9allocatorIS1_EEE26__swap_out_circular_bufferERNS_14__split_bufferIS1_RS3_EE(%"class.std::__1::vector.2"* %this1, %"struct.std::__1::__split_buffer.15"* nonnull align 8 dereferenceable(40) %__v)
  br label %invoke.cont9

invoke.cont9:                                     ; preds = %invoke.cont
  %call10 = call %"struct.std::__1::__split_buffer.15"* @_ZNSt3__114__split_bufferI4RoleRNS_9allocatorIS1_EEED1Ev(%"struct.std::__1::__split_buffer.15"* %__v) #14
  ret void
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE9constructIS2_JRKS2_EEEvRS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  %agg.tmp = alloca %"struct.std::__1::integral_constant", align 1
  %ref.tmp = alloca %"struct.std::__1::__has_construct.20", align 1
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %i = bitcast %"struct.std::__1::__has_construct.20"* %ref.tmp to %"struct.std::__1::integral_constant"*
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE11__constructIS2_JRKS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %i1, %struct.Role* %i2, %struct.Role* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %struct.Role*, align 8
  store %struct.Role* %__t, %struct.Role** %__t.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__t.addr, align 8
  ret %struct.Role* %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__116allocator_traitsINS_9allocatorI4RoleEEE11__constructIS2_JRKS2_EEEvNS_17integral_constantIbLb1EEERS3_PT_DpOT0_(%"class.std::__1::allocator.7"* nonnull align 1 dereferenceable(1) %__a, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #0 align 2 {
entry:
  %i = alloca %"struct.std::__1::integral_constant", align 1
  %__a.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %__a, %"class.std::__1::allocator.7"** %__a.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %i1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %__a.addr, align 8
  %i2 = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  call void @_ZNSt3__19allocatorI4RoleE9constructIS1_JRKS1_EEEvPT_DpOT0_(%"class.std::__1::allocator.7"* %i1, %struct.Role* %i2, %struct.Role* nonnull align 4 dereferenceable(8) %call)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr void @_ZNSt3__19allocatorI4RoleE9constructIS1_JRKS1_EEEvPT_DpOT0_(%"class.std::__1::allocator.7"* %this, %struct.Role* %__p, %struct.Role* nonnull align 4 dereferenceable(8) %__args) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.7"*, align 8
  %__p.addr = alloca %struct.Role*, align 8
  %__args.addr = alloca %struct.Role*, align 8
  store %"class.std::__1::allocator.7"* %this, %"class.std::__1::allocator.7"** %this.addr, align 8
  store %struct.Role* %__p, %struct.Role** %__p.addr, align 8
  store %struct.Role* %__args, %struct.Role** %__args.addr, align 8
  %this1 = load %"class.std::__1::allocator.7"*, %"class.std::__1::allocator.7"** %this.addr, align 8
  %i = load %struct.Role*, %struct.Role** %__p.addr, align 8
  %i1 = bitcast %struct.Role* %i to i8*
  %i2 = bitcast i8* %i1 to %struct.Role*
  %i3 = load %struct.Role*, %struct.Role** %__args.addr, align 8
  %call = call nonnull align 4 dereferenceable(8) %struct.Role* @_ZNSt3__17forwardIRK4RoleEEOT_RNS_16remove_referenceIS4_E4typeE(%struct.Role* nonnull align 4 dereferenceable(8) %i3) #14
  %i4 = bitcast %struct.Role* %i2 to i8*
  %i5 = bitcast %struct.Role* %call to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %i4, i8* align 4 %i5, i64 8, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__16vectorI4UserNS_9allocatorIS1_EEE11__make_iterEPS1_(%"class.std::__1::vector"* %this, %struct.User* %__p) #1 align 2 {
entry:
  %retval = alloca %"class.std::__1::__wrap_iter.9", align 8
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__p.addr = alloca %struct.User*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store %struct.User* %__p, %struct.User** %__p.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__p.addr, align 8
  %call = call %"class.std::__1::__wrap_iter.9"* @_ZNSt3__111__wrap_iterIP4UserEC1ES2_(%"class.std::__1::__wrap_iter.9"* %retval, %struct.User* %i) #14
  %coerce.dive = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %retval, i32 0, i32 0
  %i1 = load %struct.User*, %struct.User** %coerce.dive, align 8
  %coerce.val.pi = ptrtoint %struct.User* %i1 to i64
  ret i64 %coerce.val.pi
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__wrap_iter.9"* @_ZNSt3__111__wrap_iterIP4UserEC1ES2_(%"class.std::__1::__wrap_iter.9"* returned %this, %struct.User* %__x) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  store %"class.std::__1::__wrap_iter.9"* %this, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  %i = load %struct.User*, %struct.User** %__x.addr, align 8
  %call = call %"class.std::__1::__wrap_iter.9"* @_ZNSt3__111__wrap_iterIP4UserEC2ES2_(%"class.std::__1::__wrap_iter.9"* %this1, %struct.User* %i) #14
  ret %"class.std::__1::__wrap_iter.9"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__wrap_iter.9"* @_ZNSt3__111__wrap_iterIP4UserEC2ES2_(%"class.std::__1::__wrap_iter.9"* returned %this, %struct.User* %__x) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__wrap_iter.9"*, align 8
  %__x.addr = alloca %struct.User*, align 8
  store %"class.std::__1::__wrap_iter.9"* %this, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  store %struct.User* %__x, %struct.User** %__x.addr, align 8
  %this1 = load %"class.std::__1::__wrap_iter.9"*, %"class.std::__1::__wrap_iter.9"** %this.addr, align 8
  %__i = getelementptr inbounds %"class.std::__1::__wrap_iter.9", %"class.std::__1::__wrap_iter.9"* %this1, i32 0, i32 0
  %i = load %struct.User*, %struct.User** %__x.addr, align 8
  store %struct.User* %i, %struct.User** %__i, align 8
  ret %"class.std::__1::__wrap_iter.9"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__124__put_character_sequenceIcNS_11char_traitsIcEEEERNS_13basic_ostreamIT_T0_EES7_PKS4_m(%"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %__os, i8* %__str, i64 %__len) #0 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %__os.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  %__str.addr = alloca i8*, align 8
  %__len.addr = alloca i64, align 8
  %__s = alloca %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  %ref.tmp = alloca %"class.std::__1::ostreambuf_iterator", align 8
  %agg.tmp = alloca %"class.std::__1::ostreambuf_iterator", align 8
  store %"class.std::__1::basic_ostream"* %__os, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  store i8* %__str, i8** %__str.addr, align 8
  store i64 %__len, i64* %__len.addr, align 8
  %i = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %call = call %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentryC1ERS3_(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %__s, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %i)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %call3 = call zeroext i1 @_ZNKSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentrycvbEv(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %__s)
  br label %invoke.cont2

invoke.cont2:                                     ; preds = %invoke.cont
  br i1 %call3, label %bb, label %bb30

if.then:                                          ; preds = %bb
  %i1 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %call4 = call %"class.std::__1::ostreambuf_iterator"* @_ZNSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEEC1ERNS_13basic_ostreamIcS2_EE(%"class.std::__1::ostreambuf_iterator"* %agg.tmp, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %i1) #14
  %i2 = load i8*, i8** %__str.addr, align 8
  %i3 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i4 = bitcast %"class.std::__1::basic_ostream"* %i3 to i8**
  %vtable = load i8*, i8** %i4, align 8
  %vbase.offset.ptr = getelementptr i8, i8* %vtable, i64 -24
  %i5 = bitcast i8* %vbase.offset.ptr to i64*
  %vbase.offset = load i64, i64* %i5, align 8
  %i6 = bitcast %"class.std::__1::basic_ostream"* %i3 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i6, i64 %vbase.offset
  %i7 = bitcast i8* %add.ptr to %"class.std::__1::ios_base"*
  %call6 = call i32 @_ZNKSt3__18ios_base5flagsEv(%"class.std::__1::ios_base"* %i7)
  br label %invoke.cont5

invoke.cont5:                                     ; preds = %if.then
  %and = and i32 %call6, 176
  %cmp = icmp eq i32 %and, 32
  br i1 %cmp, label %bb31, label %bb32

cond.true:                                        ; preds = %bb31
  %i8 = load i8*, i8** %__str.addr, align 8
  %i9 = load i64, i64* %__len.addr, align 8
  %add.ptr7 = getelementptr i8, i8* %i8, i64 %i9
  br label %cond.end

cond.false:                                       ; preds = %bb32
  %i10 = load i8*, i8** %__str.addr, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i8* [ %add.ptr7, %cond.true ], [ %i10, %cond.false ]
  %i11 = load i8*, i8** %__str.addr, align 8
  %i12 = load i64, i64* %__len.addr, align 8
  %add.ptr8 = getelementptr i8, i8* %i11, i64 %i12
  %i13 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i14 = bitcast %"class.std::__1::basic_ostream"* %i13 to i8**
  %vtable9 = load i8*, i8** %i14, align 8
  %vbase.offset.ptr10 = getelementptr i8, i8* %vtable9, i64 -24
  %i15 = bitcast i8* %vbase.offset.ptr10 to i64*
  %vbase.offset11 = load i64, i64* %i15, align 8
  %i16 = bitcast %"class.std::__1::basic_ostream"* %i13 to i8*
  %add.ptr12 = getelementptr inbounds i8, i8* %i16, i64 %vbase.offset11
  %i17 = bitcast i8* %add.ptr12 to %"class.std::__1::ios_base"*
  %i18 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i19 = bitcast %"class.std::__1::basic_ostream"* %i18 to i8**
  %vtable13 = load i8*, i8** %i19, align 8
  %vbase.offset.ptr14 = getelementptr i8, i8* %vtable13, i64 -24
  %i20 = bitcast i8* %vbase.offset.ptr14 to i64*
  %vbase.offset15 = load i64, i64* %i20, align 8
  %i21 = bitcast %"class.std::__1::basic_ostream"* %i18 to i8*
  %add.ptr16 = getelementptr inbounds i8, i8* %i21, i64 %vbase.offset15
  %i22 = bitcast i8* %add.ptr16 to %"class.std::__1::basic_ios"*
  %call18 = call signext i8 @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE4fillEv(%"class.std::__1::basic_ios"* %i22)
  br label %invoke.cont17

invoke.cont17:                                    ; preds = %cond.end
  %coerce.dive = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %agg.tmp, i32 0, i32 0
  %i23 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %coerce.dive, align 8
  %coerce.val.pi = ptrtoint %"class.std::__1::basic_streambuf"* %i23 to i64
  %call20 = call i64 @_ZNSt3__116__pad_and_outputIcNS_11char_traitsIcEEEENS_19ostreambuf_iteratorIT_T0_EES6_PKS4_S8_S8_RNS_8ios_baseES4_(i64 %coerce.val.pi, i8* %i2, i8* %cond, i8* %add.ptr8, %"class.std::__1::ios_base"* nonnull align 8 dereferenceable(136) %i17, i8 signext %call18)
  br label %invoke.cont19

invoke.cont19:                                    ; preds = %invoke.cont17
  %coerce.dive21 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %ref.tmp, i32 0, i32 0
  %coerce.val.ip = inttoptr i64 %call20 to %"class.std::__1::basic_streambuf"*
  store %"class.std::__1::basic_streambuf"* %coerce.val.ip, %"class.std::__1::basic_streambuf"** %coerce.dive21, align 8
  %call22 = call zeroext i1 @_ZNKSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEE6failedEv(%"class.std::__1::ostreambuf_iterator"* %ref.tmp) #14
  br i1 %call22, label %bb33, label %bb34

if.then23:                                        ; preds = %bb33
  %i24 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  %i25 = bitcast %"class.std::__1::basic_ostream"* %i24 to i8**
  %vtable24 = load i8*, i8** %i25, align 8
  %vbase.offset.ptr25 = getelementptr i8, i8* %vtable24, i64 -24
  %i26 = bitcast i8* %vbase.offset.ptr25 to i64*
  %vbase.offset26 = load i64, i64* %i26, align 8
  %i27 = bitcast %"class.std::__1::basic_ostream"* %i24 to i8*
  %add.ptr27 = getelementptr inbounds i8, i8* %i27, i64 %vbase.offset26
  %i28 = bitcast i8* %add.ptr27 to %"class.std::__1::basic_ios"*
  call void @_ZNSt3__19basic_iosIcNS_11char_traitsIcEEE8setstateEj(%"class.std::__1::basic_ios"* %i28, i32 5)
  br label %invoke.cont28

invoke.cont28:                                    ; preds = %if.then23
  br label %if.end

try.cont:                                         ; preds = %if.end29
  %i29 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__os.addr, align 8
  ret %"class.std::__1::basic_ostream"* %i29

if.end:                                           ; preds = %bb34, %invoke.cont28
  br label %if.end29

if.end29:                                         ; preds = %bb30, %if.end
  %call30 = call %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentryD1Ev(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %__s) #14
  br label %try.cont

bb:                                               ; preds = %invoke.cont2
  br label %if.then

bb30:                                             ; preds = %invoke.cont2
  br label %if.end29

bb31:                                             ; preds = %invoke.cont5
  br label %cond.true

bb32:                                             ; preds = %invoke.cont5
  br label %cond.false

bb33:                                             ; preds = %invoke.cont19
  br label %if.then23

bb34:                                             ; preds = %invoke.cont19
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i64 @_ZNSt3__111char_traitsIcE6lengthEPKc(i8* %__s) #1 align 2 {
entry:
  %__s.addr = alloca i8*, align 8
  store i8* %__s, i8** %__s.addr, align 8
  %i = load i8*, i8** %__s.addr, align 8
  %call = call i64 @strlen(i8* %i) #14
  ret i64 %call
}

declare %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentryC1ERS3_(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* returned, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8)) unnamed_addr #4

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentrycvbEv(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"*, align 8
  store %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %this, %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"*, %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"** %this.addr, align 8
  %__ok_ = getelementptr inbounds %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry", %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* %this1, i32 0, i32 0
  %i = load i8, i8* %__ok_, align 8
  %tobool = trunc i8 %i to i1
  ret i1 %tobool
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__116__pad_and_outputIcNS_11char_traitsIcEEEENS_19ostreambuf_iteratorIT_T0_EES6_PKS4_S8_S8_RNS_8ios_baseES4_(i64 %__s.coerce, i8* %__ob, i8* %__op, i8* %__oe, %"class.std::__1::ios_base"* nonnull align 8 dereferenceable(136) %__iob, i8 signext %__fl) #0 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %retval = alloca %"class.std::__1::ostreambuf_iterator", align 8
  %__s = alloca %"class.std::__1::ostreambuf_iterator", align 8
  %__ob.addr = alloca i8*, align 8
  %__op.addr = alloca i8*, align 8
  %__oe.addr = alloca i8*, align 8
  %__iob.addr = alloca %"class.std::__1::ios_base"*, align 8
  %__fl.addr = alloca i8, align 1
  %__sz = alloca i64, align 8
  %__ns = alloca i64, align 8
  %__np = alloca i64, align 8
  %__sp = alloca %"class.std::__1::basic_string", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  %cleanup.dest.slot = alloca i32, align 4
  %coerce.dive = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  %coerce.val.ip = inttoptr i64 %__s.coerce to %"class.std::__1::basic_streambuf"*
  store %"class.std::__1::basic_streambuf"* %coerce.val.ip, %"class.std::__1::basic_streambuf"** %coerce.dive, align 8
  store i8* %__ob, i8** %__ob.addr, align 8
  store i8* %__op, i8** %__op.addr, align 8
  store i8* %__oe, i8** %__oe.addr, align 8
  store %"class.std::__1::ios_base"* %__iob, %"class.std::__1::ios_base"** %__iob.addr, align 8
  store i8 %__fl, i8* %__fl.addr, align 1
  %__sbuf_ = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  %i = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %__sbuf_, align 8
  %cmp = icmp eq %"class.std::__1::basic_streambuf"* %i, null
  br i1 %cmp, label %bb, label %bb40

if.then:                                          ; preds = %bb
  %i1 = bitcast %"class.std::__1::ostreambuf_iterator"* %retval to i8*
  %i2 = bitcast %"class.std::__1::ostreambuf_iterator"* %__s to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i1, i8* align 8 %i2, i64 8, i1 false)
  br label %return

if.end:                                           ; preds = %bb40
  %i3 = load i8*, i8** %__oe.addr, align 8
  %i4 = load i8*, i8** %__ob.addr, align 8
  %sub.ptr.lhs.cast = ptrtoint i8* %i3 to i64
  %sub.ptr.rhs.cast = ptrtoint i8* %i4 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  store i64 %sub.ptr.sub, i64* %__sz, align 8
  %i5 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %__iob.addr, align 8
  %call = call i64 @_ZNKSt3__18ios_base5widthEv(%"class.std::__1::ios_base"* %i5)
  store i64 %call, i64* %__ns, align 8
  %i6 = load i64, i64* %__ns, align 8
  %i7 = load i64, i64* %__sz, align 8
  %cmp1 = icmp sgt i64 %i6, %i7
  br i1 %cmp1, label %bb41, label %bb42

if.then2:                                         ; preds = %bb41
  %i8 = load i64, i64* %__sz, align 8
  %i9 = load i64, i64* %__ns, align 8
  %sub = sub i64 %i9, %i8
  store i64 %sub, i64* %__ns, align 8
  br label %if.end3

if.else:                                          ; preds = %bb42
  store i64 0, i64* %__ns, align 8
  br label %if.end3

if.end3:                                          ; preds = %if.else, %if.then2
  %i10 = load i8*, i8** %__op.addr, align 8
  %i11 = load i8*, i8** %__ob.addr, align 8
  %sub.ptr.lhs.cast4 = ptrtoint i8* %i10 to i64
  %sub.ptr.rhs.cast5 = ptrtoint i8* %i11 to i64
  %sub.ptr.sub6 = sub i64 %sub.ptr.lhs.cast4, %sub.ptr.rhs.cast5
  store i64 %sub.ptr.sub6, i64* %__np, align 8
  %i12 = load i64, i64* %__np, align 8
  %cmp7 = icmp sgt i64 %i12, 0
  br i1 %cmp7, label %bb43, label %bb44

if.then8:                                         ; preds = %bb43
  %__sbuf_9 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  %i13 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %__sbuf_9, align 8
  %i14 = load i8*, i8** %__ob.addr, align 8
  %i15 = load i64, i64* %__np, align 8
  %call10 = call i64 @_ZNSt3__115basic_streambufIcNS_11char_traitsIcEEE5sputnEPKcl(%"class.std::__1::basic_streambuf"* %i13, i8* %i14, i64 %i15)
  %i16 = load i64, i64* %__np, align 8
  %cmp11 = icmp ne i64 %call10, %i16
  br i1 %cmp11, label %bb45, label %bb46

if.then12:                                        ; preds = %bb45
  %__sbuf_13 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  store %"class.std::__1::basic_streambuf"* null, %"class.std::__1::basic_streambuf"** %__sbuf_13, align 8
  %i17 = bitcast %"class.std::__1::ostreambuf_iterator"* %retval to i8*
  %i18 = bitcast %"class.std::__1::ostreambuf_iterator"* %__s to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i17, i8* align 8 %i18, i64 8, i1 false)
  br label %return

if.end14:                                         ; preds = %bb46
  br label %if.end15

if.end15:                                         ; preds = %bb44, %if.end14
  %i19 = load i64, i64* %__ns, align 8
  %cmp16 = icmp sgt i64 %i19, 0
  br i1 %cmp16, label %bb47, label %bb48

if.then17:                                        ; preds = %bb47
  %i20 = load i64, i64* %__ns, align 8
  %i21 = load i8, i8* %__fl.addr, align 1
  %call18 = call %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEEC1Emc(%"class.std::__1::basic_string"* %__sp, i64 %i20, i8 signext %i21)
  %__sbuf_19 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  %i22 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %__sbuf_19, align 8
  %call20 = call i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE4dataEv(%"class.std::__1::basic_string"* %__sp) #14
  %i23 = load i64, i64* %__ns, align 8
  %call21 = call i64 @_ZNSt3__115basic_streambufIcNS_11char_traitsIcEEE5sputnEPKcl(%"class.std::__1::basic_streambuf"* %i22, i8* %call20, i64 %i23)
  br label %invoke.cont

invoke.cont:                                      ; preds = %if.then17
  %i24 = load i64, i64* %__ns, align 8
  %cmp22 = icmp ne i64 %call21, %i24
  br i1 %cmp22, label %bb49, label %bb50

if.then23:                                        ; preds = %bb49
  %__sbuf_24 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  store %"class.std::__1::basic_streambuf"* null, %"class.std::__1::basic_streambuf"** %__sbuf_24, align 8
  %i25 = bitcast %"class.std::__1::ostreambuf_iterator"* %retval to i8*
  %i26 = bitcast %"class.std::__1::ostreambuf_iterator"* %__s to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i25, i8* align 8 %i26, i64 8, i1 false)
  store i32 1, i32* %cleanup.dest.slot, align 4
  br label %cleanup

if.end25:                                         ; preds = %bb50
  store i32 0, i32* %cleanup.dest.slot, align 4
  br label %cleanup

cleanup:                                          ; preds = %if.end25, %if.then23
  %call26 = call %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEED1Ev(%"class.std::__1::basic_string"* %__sp) #14
  %cleanup.dest = load i32, i32* %cleanup.dest.slot, align 4
  switch i32 %cleanup.dest, label %unreachable [
    i32 0, label %cleanup.cont
    i32 1, label %return
  ]

cleanup.cont:                                     ; preds = %cleanup
  br label %if.end28

if.end28:                                         ; preds = %bb48, %cleanup.cont
  %i27 = load i8*, i8** %__oe.addr, align 8
  %i28 = load i8*, i8** %__op.addr, align 8
  %sub.ptr.lhs.cast29 = ptrtoint i8* %i27 to i64
  %sub.ptr.rhs.cast30 = ptrtoint i8* %i28 to i64
  %sub.ptr.sub31 = sub i64 %sub.ptr.lhs.cast29, %sub.ptr.rhs.cast30
  store i64 %sub.ptr.sub31, i64* %__np, align 8
  %i29 = load i64, i64* %__np, align 8
  %cmp32 = icmp sgt i64 %i29, 0
  br i1 %cmp32, label %bb51, label %bb52

if.then33:                                        ; preds = %bb51
  %__sbuf_34 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  %i30 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %__sbuf_34, align 8
  %i31 = load i8*, i8** %__op.addr, align 8
  %i32 = load i64, i64* %__np, align 8
  %call35 = call i64 @_ZNSt3__115basic_streambufIcNS_11char_traitsIcEEE5sputnEPKcl(%"class.std::__1::basic_streambuf"* %i30, i8* %i31, i64 %i32)
  %i33 = load i64, i64* %__np, align 8
  %cmp36 = icmp ne i64 %call35, %i33
  br i1 %cmp36, label %bb53, label %bb54

if.then37:                                        ; preds = %bb53
  %__sbuf_38 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %__s, i32 0, i32 0
  store %"class.std::__1::basic_streambuf"* null, %"class.std::__1::basic_streambuf"** %__sbuf_38, align 8
  %i34 = bitcast %"class.std::__1::ostreambuf_iterator"* %retval to i8*
  %i35 = bitcast %"class.std::__1::ostreambuf_iterator"* %__s to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i34, i8* align 8 %i35, i64 8, i1 false)
  br label %return

if.end39:                                         ; preds = %bb54
  br label %if.end40

if.end40:                                         ; preds = %bb52, %if.end39
  %i36 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %__iob.addr, align 8
  %call41 = call i64 @_ZNSt3__18ios_base5widthEl(%"class.std::__1::ios_base"* %i36, i64 0)
  %i37 = bitcast %"class.std::__1::ostreambuf_iterator"* %retval to i8*
  %i38 = bitcast %"class.std::__1::ostreambuf_iterator"* %__s to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i37, i8* align 8 %i38, i64 8, i1 false)
  br label %return

return:                                           ; preds = %if.end40, %if.then37, %cleanup, %if.then12, %if.then
  %coerce.dive42 = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %retval, i32 0, i32 0
  %i39 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %coerce.dive42, align 8
  %coerce.val.pi = ptrtoint %"class.std::__1::basic_streambuf"* %i39 to i64
  ret i64 %coerce.val.pi

unreachable:                                      ; preds = %cleanup
  unreachable

bb:                                               ; preds = %entry
  br label %if.then

bb40:                                             ; preds = %entry
  br label %if.end

bb41:                                             ; preds = %if.end
  br label %if.then2

bb42:                                             ; preds = %if.end
  br label %if.else

bb43:                                             ; preds = %if.end3
  br label %if.then8

bb44:                                             ; preds = %if.end3
  br label %if.end15

bb45:                                             ; preds = %if.then8
  br label %if.then12

bb46:                                             ; preds = %if.then8
  br label %if.end14

bb47:                                             ; preds = %if.end15
  br label %if.then17

bb48:                                             ; preds = %if.end15
  br label %if.end28

bb49:                                             ; preds = %invoke.cont
  br label %if.then23

bb50:                                             ; preds = %invoke.cont
  br label %if.end25

bb51:                                             ; preds = %if.end28
  br label %if.then33

bb52:                                             ; preds = %if.end28
  br label %if.end40

bb53:                                             ; preds = %if.then33
  br label %if.then37

bb54:                                             ; preds = %if.then33
  br label %if.end39
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::ostreambuf_iterator"* @_ZNSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEEC1ERNS_13basic_ostreamIcS2_EE(%"class.std::__1::ostreambuf_iterator"* returned %this, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %__s) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ostreambuf_iterator"*, align 8
  %__s.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  store %"class.std::__1::ostreambuf_iterator"* %this, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  store %"class.std::__1::basic_ostream"* %__s, %"class.std::__1::basic_ostream"** %__s.addr, align 8
  %this1 = load %"class.std::__1::ostreambuf_iterator"*, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  %i = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__s.addr, align 8
  %call = call %"class.std::__1::ostreambuf_iterator"* @_ZNSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEEC2ERNS_13basic_ostreamIcS2_EE(%"class.std::__1::ostreambuf_iterator"* %this1, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %i) #14
  ret %"class.std::__1::ostreambuf_iterator"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i32 @_ZNKSt3__18ios_base5flagsEv(%"class.std::__1::ios_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ios_base"*, align 8
  store %"class.std::__1::ios_base"* %this, %"class.std::__1::ios_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %this.addr, align 8
  %__fmtflags_ = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 1
  %i = load i32, i32* %__fmtflags_, align 8
  ret i32 %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden signext i8 @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE4fillEv(%"class.std::__1::basic_ios"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_ios"*, align 8
  store %"class.std::__1::basic_ios"* %this, %"class.std::__1::basic_ios"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_ios"*, %"class.std::__1::basic_ios"** %this.addr, align 8
  %call = call i32 @_ZNSt3__111char_traitsIcE3eofEv() #14
  %__fill_ = getelementptr inbounds %"class.std::__1::basic_ios", %"class.std::__1::basic_ios"* %this1, i32 0, i32 2
  %i = load i32, i32* %__fill_, align 8
  %call2 = call zeroext i1 @_ZNSt3__111char_traitsIcE11eq_int_typeEii(i32 %call, i32 %i) #14
  br i1 %call2, label %bb, label %bb2

if.then:                                          ; preds = %bb
  %call3 = call signext i8 @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE5widenEc(%"class.std::__1::basic_ios"* %this1, i8 signext 32)
  %conv = sext i8 %call3 to i32
  %__fill_4 = getelementptr inbounds %"class.std::__1::basic_ios", %"class.std::__1::basic_ios"* %this1, i32 0, i32 2
  store i32 %conv, i32* %__fill_4, align 8
  br label %if.end

if.end:                                           ; preds = %bb2, %if.then
  %__fill_5 = getelementptr inbounds %"class.std::__1::basic_ios", %"class.std::__1::basic_ios"* %this1, i32 0, i32 2
  %i1 = load i32, i32* %__fill_5, align 8
  %conv6 = trunc i32 %i1 to i8
  ret i8 %conv6

bb:                                               ; preds = %entry
  br label %if.then

bb2:                                              ; preds = %entry
  br label %if.end
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEE6failedEv(%"class.std::__1::ostreambuf_iterator"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ostreambuf_iterator"*, align 8
  store %"class.std::__1::ostreambuf_iterator"* %this, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  %this1 = load %"class.std::__1::ostreambuf_iterator"*, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  %__sbuf_ = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %__sbuf_, align 8
  %cmp = icmp eq %"class.std::__1::basic_streambuf"* %i, null
  ret i1 %cmp
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19basic_iosIcNS_11char_traitsIcEEE8setstateEj(%"class.std::__1::basic_ios"* %this, i32 %__state) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_ios"*, align 8
  %__state.addr = alloca i32, align 4
  store %"class.std::__1::basic_ios"* %this, %"class.std::__1::basic_ios"** %this.addr, align 8
  store i32 %__state, i32* %__state.addr, align 4
  %this1 = load %"class.std::__1::basic_ios"*, %"class.std::__1::basic_ios"** %this.addr, align 8
  %i = bitcast %"class.std::__1::basic_ios"* %this1 to %"class.std::__1::ios_base"*
  %i1 = load i32, i32* %__state.addr, align 4
  call void @_ZNSt3__18ios_base8setstateEj(%"class.std::__1::ios_base"* %i, i32 %i1)
  ret void
}

; Function Attrs: nounwind
declare %"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE6sentryD1Ev(%"class.std::__1::basic_ostream<char, std::__1::char_traits<char>>::sentry"* returned) unnamed_addr #10

declare void @_ZNSt3__18ios_base33__set_badbit_and_consider_rethrowEv(%"class.std::__1::ios_base"*) #4

declare void @__cxa_end_catch()

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__18ios_base5widthEv(%"class.std::__1::ios_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ios_base"*, align 8
  store %"class.std::__1::ios_base"* %this, %"class.std::__1::ios_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %this.addr, align 8
  %__width_ = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 3
  %i = load i64, i64* %__width_, align 8
  ret i64 %i
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__115basic_streambufIcNS_11char_traitsIcEEE5sputnEPKcl(%"class.std::__1::basic_streambuf"* %this, i8* %__s, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_streambuf"*, align 8
  %__s.addr = alloca i8*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::basic_streambuf"* %this, %"class.std::__1::basic_streambuf"** %this.addr, align 8
  store i8* %__s, i8** %__s.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::basic_streambuf"*, %"class.std::__1::basic_streambuf"** %this.addr, align 8
  %i = load i8*, i8** %__s.addr, align 8
  %i1 = load i64, i64* %__n.addr, align 8
  %i2 = bitcast %"class.std::__1::basic_streambuf"* %this1 to i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)***
  %vtable = load i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)**, i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)*** %i2, align 8
  %vfn = getelementptr inbounds i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)*, i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)** %vtable, i64 12
  %i3 = load i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)*, i64 (%"class.std::__1::basic_streambuf"*, i8*, i64)** %vfn, align 8
  %call = call i64 %i3(%"class.std::__1::basic_streambuf"* %this1, i8* %i, i64 %i1)
  ret i64 %call
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEEC1Emc(%"class.std::__1::basic_string"* returned %this, i64 %__n, i8 signext %__c) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  %__n.addr = alloca i64, align 8
  %__c.addr = alloca i8, align 1
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  store i8 %__c, i8* %__c.addr, align 1
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %i = load i64, i64* %__n.addr, align 8
  %i1 = load i8, i8* %__c.addr, align 1
  %call = call %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEEC2Emc(%"class.std::__1::basic_string"* %this1, i64 %i, i8 signext %i1)
  ret %"class.std::__1::basic_string"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE4dataEv(%"class.std::__1::basic_string"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %call = call i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE13__get_pointerEv(%"class.std::__1::basic_string"* %this1) #14
  %call2 = call i8* @_ZNSt3__112__to_addressIcEEPT_S2_(i8* %call) #14
  ret i8* %call2
}

; Function Attrs: nounwind
declare %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEED1Ev(%"class.std::__1::basic_string"* returned) unnamed_addr #10

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__18ios_base5widthEl(%"class.std::__1::ios_base"* %this, i64 %__wide) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ios_base"*, align 8
  %__wide.addr = alloca i64, align 8
  %__r = alloca i64, align 8
  store %"class.std::__1::ios_base"* %this, %"class.std::__1::ios_base"** %this.addr, align 8
  store i64 %__wide, i64* %__wide.addr, align 8
  %this1 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %this.addr, align 8
  %__width_ = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 3
  %i = load i64, i64* %__width_, align 8
  store i64 %i, i64* %__r, align 8
  %i1 = load i64, i64* %__wide.addr, align 8
  %__width_2 = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 3
  store i64 %i1, i64* %__width_2, align 8
  %i2 = load i64, i64* %__r, align 8
  ret i64 %i2
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::basic_string"* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEEC2Emc(%"class.std::__1::basic_string"* returned %this, i64 %__n, i8 signext %__c) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  %__n.addr = alloca i64, align 8
  %__c.addr = alloca i8, align 1
  %ref.tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  %ref.tmp2 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  store i8 %__c, i8* %__c.addr, align 1
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %i = bitcast %"class.std::__1::basic_string"* %this1 to %"class.std::__1::__basic_string_common"*
  %__r_ = getelementptr inbounds %"class.std::__1::basic_string", %"class.std::__1::basic_string"* %this1, i32 0, i32 0
  %call = call %"class.std::__1::__compressed_pair.21"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_EC1INS_18__default_init_tagESA_EEOT_OT0_(%"class.std::__1::__compressed_pair.21"* %__r_, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %ref.tmp2)
  %i1 = load i64, i64* %__n.addr, align 8
  %i2 = load i8, i8* %__c.addr, align 1
  call void @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE6__initEmc(%"class.std::__1::basic_string"* %this1, i64 %i1, i8 signext %i2)
  ret %"class.std::__1::basic_string"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.21"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_EC1INS_18__default_init_tagESA_EEOT_OT0_(%"class.std::__1::__compressed_pair.21"* returned %this, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.21"*, align 8
  %__t1.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  store %"class.std::__1::__compressed_pair.21"* %this, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t1, %"struct.std::__1::__default_init_tag"** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.21"*, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %i = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t1.addr, align 8
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call = call %"class.std::__1::__compressed_pair.21"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_EC2INS_18__default_init_tagESA_EEOT_OT0_(%"class.std::__1::__compressed_pair.21"* %this1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1)
  ret %"class.std::__1::__compressed_pair.21"* %this1
}

declare void @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE6__initEmc(%"class.std::__1::basic_string"*, i64, i8 signext) #4

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__compressed_pair.21"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_EC2INS_18__default_init_tagESA_EEOT_OT0_(%"class.std::__1::__compressed_pair.21"* returned %this, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t1, %"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %__t2) unnamed_addr #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.21"*, align 8
  %__t1.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %__t2.addr = alloca %"struct.std::__1::__default_init_tag"*, align 8
  %agg.tmp = alloca %"struct.std::__1::__default_init_tag", align 1
  %agg.tmp3 = alloca %"struct.std::__1::__default_init_tag", align 1
  store %"class.std::__1::__compressed_pair.21"* %this, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t1, %"struct.std::__1::__default_init_tag"** %__t1.addr, align 8
  store %"struct.std::__1::__default_init_tag"* %__t2, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.21"*, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.21"* %this1 to %"struct.std::__1::__compressed_pair_elem.22"*
  %i1 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t1.addr, align 8
  %call = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i1) #14
  %call2 = call %"struct.std::__1::__compressed_pair_elem.22"* @_ZNSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.22"* %i)
  %i2 = bitcast %"class.std::__1::__compressed_pair.21"* %this1 to %"struct.std::__1::__compressed_pair_elem.23"*
  %i3 = load %"struct.std::__1::__default_init_tag"*, %"struct.std::__1::__default_init_tag"** %__t2.addr, align 8
  %call4 = call nonnull align 1 dereferenceable(1) %"struct.std::__1::__default_init_tag"* @_ZNSt3__17forwardINS_18__default_init_tagEEEOT_RNS_16remove_referenceIS2_E4typeE(%"struct.std::__1::__default_init_tag"* nonnull align 1 dereferenceable(1) %i3) #14
  %call5 = call %"struct.std::__1::__compressed_pair_elem.23"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIcEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.23"* %i2)
  ret %"class.std::__1::__compressed_pair.21"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__compressed_pair_elem.22"* @_ZNSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.22"* returned %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.22"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.22"* %this, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.22"*, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.22", %"struct.std::__1::__compressed_pair_elem.22"* %this1, i32 0, i32 0
  ret %"struct.std::__1::__compressed_pair_elem.22"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__compressed_pair_elem.23"* @_ZNSt3__122__compressed_pair_elemINS_9allocatorIcEELi1ELb1EEC2ENS_18__default_init_tagE(%"struct.std::__1::__compressed_pair_elem.23"* returned %this) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__default_init_tag", align 1
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.23"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.23"* %this, %"struct.std::__1::__compressed_pair_elem.23"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.23"*, %"struct.std::__1::__compressed_pair_elem.23"** %this.addr, align 8
  %i1 = bitcast %"struct.std::__1::__compressed_pair_elem.23"* %this1 to %"class.std::__1::allocator.24"*
  %call = call %"class.std::__1::allocator.24"* @_ZNSt3__19allocatorIcEC2Ev(%"class.std::__1::allocator.24"* %i1) #14
  ret %"struct.std::__1::__compressed_pair_elem.23"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::allocator.24"* @_ZNSt3__19allocatorIcEC2Ev(%"class.std::__1::allocator.24"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::allocator.24"*, align 8
  store %"class.std::__1::allocator.24"* %this, %"class.std::__1::allocator.24"** %this.addr, align 8
  %this1 = load %"class.std::__1::allocator.24"*, %"class.std::__1::allocator.24"** %this.addr, align 8
  ret %"class.std::__1::allocator.24"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__112__to_addressIcEEPT_S2_(i8* %__p) #1 {
entry:
  %__p.addr = alloca i8*, align 8
  store i8* %__p, i8** %__p.addr, align 8
  %i = load i8*, i8** %__p.addr, align 8
  ret i8* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE13__get_pointerEv(%"class.std::__1::basic_string"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %call = call zeroext i1 @_ZNKSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE9__is_longEv(%"class.std::__1::basic_string"* %this1) #14
  br i1 %call, label %bb, label %bb1

cond.true:                                        ; preds = %bb
  %call2 = call i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE18__get_long_pointerEv(%"class.std::__1::basic_string"* %this1) #14
  br label %cond.end

cond.false:                                       ; preds = %bb1
  %call3 = call i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE19__get_short_pointerEv(%"class.std::__1::basic_string"* %this1) #14
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i8* [ %call2, %cond.true ], [ %call3, %cond.false ]
  ret i8* %cond

bb:                                               ; preds = %entry
  br label %cond.true

bb1:                                              ; preds = %entry
  br label %cond.false
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden zeroext i1 @_ZNKSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE9__is_longEv(%"class.std::__1::basic_string"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %__r_ = getelementptr inbounds %"class.std::__1::basic_string", %"class.std::__1::basic_string"* %this1, i32 0, i32 0
  %call = call nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNKSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_E5firstEv(%"class.std::__1::__compressed_pair.21"* %__r_) #14
  %i = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %call, i32 0, i32 0
  %__s = bitcast %union.anon* %i to %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short"*
  %i1 = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short"* %__s, i32 0, i32 1
  %__size_ = getelementptr inbounds %struct.anon, %struct.anon* %i1, i32 0, i32 0
  %i2 = load i8, i8* %__size_, align 1
  %conv = zext i8 %i2 to i64
  %and = and i64 %conv, 128
  %tobool = icmp ne i64 %and, 0
  ret i1 %tobool
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE18__get_long_pointerEv(%"class.std::__1::basic_string"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %__r_ = getelementptr inbounds %"class.std::__1::basic_string", %"class.std::__1::basic_string"* %this1, i32 0, i32 0
  %call = call nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_E5firstEv(%"class.std::__1::__compressed_pair.21"* %__r_) #14
  %i = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %call, i32 0, i32 0
  %__l = bitcast %union.anon* %i to %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long"*
  %__data_ = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__long"* %__l, i32 0, i32 0
  %i1 = load i8*, i8** %__data_, align 8
  ret i8* %i1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__112basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE19__get_short_pointerEv(%"class.std::__1::basic_string"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_string"*, align 8
  store %"class.std::__1::basic_string"* %this, %"class.std::__1::basic_string"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_string"*, %"class.std::__1::basic_string"** %this.addr, align 8
  %__r_ = getelementptr inbounds %"class.std::__1::basic_string", %"class.std::__1::basic_string"* %this1, i32 0, i32 0
  %call = call nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_E5firstEv(%"class.std::__1::__compressed_pair.21"* %__r_) #14
  %i = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %call, i32 0, i32 0
  %__s = bitcast %union.anon* %i to %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short"*
  %__data_ = getelementptr inbounds %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short", %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__short"* %__s, i32 0, i32 0
  %arrayidx = getelementptr [23 x i8], [23 x i8]* %__data_, i64 0, i64 0
  %call2 = call i8* @_ZNSt3__114pointer_traitsIPcE10pointer_toERc(i8* nonnull align 1 dereferenceable(1) %arrayidx) #14
  ret i8* %call2
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNKSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_E5firstEv(%"class.std::__1::__compressed_pair.21"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.21"*, align 8
  store %"class.std::__1::__compressed_pair.21"* %this, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.21"*, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.21"* %this1 to %"struct.std::__1::__compressed_pair_elem.22"*
  %call = call nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNKSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.22"* %i) #14
  ret %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNKSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.22"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.22"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.22"* %this, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.22"*, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.22", %"struct.std::__1::__compressed_pair_elem.22"* %this1, i32 0, i32 0
  ret %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %__value_
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNSt3__117__compressed_pairINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repES5_E5firstEv(%"class.std::__1::__compressed_pair.21"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__compressed_pair.21"*, align 8
  store %"class.std::__1::__compressed_pair.21"* %this, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %this1 = load %"class.std::__1::__compressed_pair.21"*, %"class.std::__1::__compressed_pair.21"** %this.addr, align 8
  %i = bitcast %"class.std::__1::__compressed_pair.21"* %this1 to %"struct.std::__1::__compressed_pair_elem.22"*
  %call = call nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.22"* %i) #14
  ret %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(24) %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* @_ZNSt3__122__compressed_pair_elemINS_12basic_stringIcNS_11char_traitsIcEENS_9allocatorIcEEE5__repELi0ELb0EE5__getEv(%"struct.std::__1::__compressed_pair_elem.22"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__compressed_pair_elem.22"*, align 8
  store %"struct.std::__1::__compressed_pair_elem.22"* %this, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__compressed_pair_elem.22"*, %"struct.std::__1::__compressed_pair_elem.22"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"struct.std::__1::__compressed_pair_elem.22", %"struct.std::__1::__compressed_pair_elem.22"* %this1, i32 0, i32 0
  ret %"struct.std::__1::basic_string<char, std::__1::char_traits<char>, std::__1::allocator<char>>::__rep"* %__value_
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__114pointer_traitsIPcE10pointer_toERc(i8* nonnull align 1 dereferenceable(1) %__r) #1 align 2 {
entry:
  %__r.addr = alloca i8*, align 8
  store i8* %__r, i8** %__r.addr, align 8
  %i = load i8*, i8** %__r.addr, align 8
  %call = call i8* @_ZNSt3__19addressofIcEEPT_RS1_(i8* nonnull align 1 dereferenceable(1) %i) #14
  ret i8* %call
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNSt3__19addressofIcEEPT_RS1_(i8* nonnull align 1 dereferenceable(1) %__x) #1 {
entry:
  %__x.addr = alloca i8*, align 8
  store i8* %__x, i8** %__x.addr, align 8
  %i = load i8*, i8** %__x.addr, align 8
  ret i8* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::ostreambuf_iterator"* @_ZNSt3__119ostreambuf_iteratorIcNS_11char_traitsIcEEEC2ERNS_13basic_ostreamIcS2_EE(%"class.std::__1::ostreambuf_iterator"* returned %this, %"class.std::__1::basic_ostream"* nonnull align 8 dereferenceable(8) %__s) unnamed_addr #1 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::ostreambuf_iterator"*, align 8
  %__s.addr = alloca %"class.std::__1::basic_ostream"*, align 8
  store %"class.std::__1::ostreambuf_iterator"* %this, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  store %"class.std::__1::basic_ostream"* %__s, %"class.std::__1::basic_ostream"** %__s.addr, align 8
  %this1 = load %"class.std::__1::ostreambuf_iterator"*, %"class.std::__1::ostreambuf_iterator"** %this.addr, align 8
  %i = bitcast %"class.std::__1::ostreambuf_iterator"* %this1 to %"struct.std::__1::iterator"*
  %__sbuf_ = getelementptr inbounds %"class.std::__1::ostreambuf_iterator", %"class.std::__1::ostreambuf_iterator"* %this1, i32 0, i32 0
  %i1 = load %"class.std::__1::basic_ostream"*, %"class.std::__1::basic_ostream"** %__s.addr, align 8
  %i2 = bitcast %"class.std::__1::basic_ostream"* %i1 to i8**
  %vtable = load i8*, i8** %i2, align 8
  %vbase.offset.ptr = getelementptr i8, i8* %vtable, i64 -24
  %i3 = bitcast i8* %vbase.offset.ptr to i64*
  %vbase.offset = load i64, i64* %i3, align 8
  %i4 = bitcast %"class.std::__1::basic_ostream"* %i1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i4, i64 %vbase.offset
  %i5 = bitcast i8* %add.ptr to %"class.std::__1::basic_ios"*
  %call = call %"class.std::__1::basic_streambuf"* @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE5rdbufEv(%"class.std::__1::basic_ios"* %i5)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  store %"class.std::__1::basic_streambuf"* %call, %"class.std::__1::basic_streambuf"** %__sbuf_, align 8
  ret %"class.std::__1::ostreambuf_iterator"* %this1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::basic_streambuf"* @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE5rdbufEv(%"class.std::__1::basic_ios"* %this) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::basic_ios"*, align 8
  store %"class.std::__1::basic_ios"* %this, %"class.std::__1::basic_ios"** %this.addr, align 8
  %this1 = load %"class.std::__1::basic_ios"*, %"class.std::__1::basic_ios"** %this.addr, align 8
  %i = bitcast %"class.std::__1::basic_ios"* %this1 to %"class.std::__1::ios_base"*
  %call = call i8* @_ZNKSt3__18ios_base5rdbufEv(%"class.std::__1::ios_base"* %i)
  %i1 = bitcast i8* %call to %"class.std::__1::basic_streambuf"*
  ret %"class.std::__1::basic_streambuf"* %i1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i8* @_ZNKSt3__18ios_base5rdbufEv(%"class.std::__1::ios_base"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ios_base"*, align 8
  store %"class.std::__1::ios_base"* %this, %"class.std::__1::ios_base"** %this.addr, align 8
  %this1 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %this.addr, align 8
  %__rdbuf_ = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 6
  %i = load i8*, i8** %__rdbuf_, align 8
  ret i8* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr zeroext i1 @_ZNSt3__111char_traitsIcE11eq_int_typeEii(i32 %__c1, i32 %__c2) #1 align 2 {
entry:
  %__c1.addr = alloca i32, align 4
  %__c2.addr = alloca i32, align 4
  store i32 %__c1, i32* %__c1.addr, align 4
  store i32 %__c2, i32* %__c2.addr, align 4
  %i = load i32, i32* %__c1.addr, align 4
  %i1 = load i32, i32* %__c2.addr, align 4
  %cmp = icmp eq i32 %i, %i1
  ret i1 %cmp
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_ZNSt3__111char_traitsIcE3eofEv() #1 align 2 {
entry:
  ret i32 -1
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden signext i8 @_ZNKSt3__19basic_iosIcNS_11char_traitsIcEEE5widenEc(%"class.std::__1::basic_ios"* %this, i8 signext %__c) #0 align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
entry:
  %this.addr = alloca %"class.std::__1::basic_ios"*, align 8
  %__c.addr = alloca i8, align 1
  %ref.tmp = alloca %"class.std::__1::locale", align 8
  %exn.slot = alloca i8*, align 8
  %ehselector.slot = alloca i32, align 4
  store %"class.std::__1::basic_ios"* %this, %"class.std::__1::basic_ios"** %this.addr, align 8
  store i8 %__c, i8* %__c.addr, align 1
  %this1 = load %"class.std::__1::basic_ios"*, %"class.std::__1::basic_ios"** %this.addr, align 8
  %i = bitcast %"class.std::__1::basic_ios"* %this1 to %"class.std::__1::ios_base"*
  call void @_ZNKSt3__18ios_base6getlocEv(%"class.std::__1::locale"* sret align 8 %ref.tmp, %"class.std::__1::ios_base"* %i)
  %call = call nonnull align 8 dereferenceable(25) %"class.std::__1::ctype"* @_ZNSt3__19use_facetINS_5ctypeIcEEEERKT_RKNS_6localeE(%"class.std::__1::locale"* nonnull align 8 dereferenceable(8) %ref.tmp)
  br label %invoke.cont

invoke.cont:                                      ; preds = %entry
  %i1 = load i8, i8* %__c.addr, align 1
  %call3 = call signext i8 @_ZNKSt3__15ctypeIcE5widenEc(%"class.std::__1::ctype"* %call, i8 signext %i1)
  br label %invoke.cont2

invoke.cont2:                                     ; preds = %invoke.cont
  %call4 = call %"class.std::__1::locale"* @_ZNSt3__16localeD1Ev(%"class.std::__1::locale"* %ref.tmp) #14
  ret i8 %call3
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 8 dereferenceable(25) %"class.std::__1::ctype"* @_ZNSt3__19use_facetINS_5ctypeIcEEEERKT_RKNS_6localeE(%"class.std::__1::locale"* nonnull align 8 dereferenceable(8) %__l) #0 {
entry:
  %__l.addr = alloca %"class.std::__1::locale"*, align 8
  store %"class.std::__1::locale"* %__l, %"class.std::__1::locale"** %__l.addr, align 8
  %i = load %"class.std::__1::locale"*, %"class.std::__1::locale"** %__l.addr, align 8
  %call = call %"class.std::__1::locale::facet"* @_ZNKSt3__16locale9use_facetERNS0_2idE(%"class.std::__1::locale"* %i, %"class.std::__1::locale::id"* nonnull align 8 dereferenceable(12) @_ZNSt3__15ctypeIcE2idE)
  %i1 = bitcast %"class.std::__1::locale::facet"* %call to %"class.std::__1::ctype"*
  ret %"class.std::__1::ctype"* %i1
}

declare void @_ZNKSt3__18ios_base6getlocEv(%"class.std::__1::locale"* sret align 8, %"class.std::__1::ios_base"*) #4

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden signext i8 @_ZNKSt3__15ctypeIcE5widenEc(%"class.std::__1::ctype"* %this, i8 signext %__c) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ctype"*, align 8
  %__c.addr = alloca i8, align 1
  store %"class.std::__1::ctype"* %this, %"class.std::__1::ctype"** %this.addr, align 8
  store i8 %__c, i8* %__c.addr, align 1
  %this1 = load %"class.std::__1::ctype"*, %"class.std::__1::ctype"** %this.addr, align 8
  %i = load i8, i8* %__c.addr, align 1
  %i1 = bitcast %"class.std::__1::ctype"* %this1 to i8 (%"class.std::__1::ctype"*, i8)***
  %vtable = load i8 (%"class.std::__1::ctype"*, i8)**, i8 (%"class.std::__1::ctype"*, i8)*** %i1, align 8
  %vfn = getelementptr inbounds i8 (%"class.std::__1::ctype"*, i8)*, i8 (%"class.std::__1::ctype"*, i8)** %vtable, i64 7
  %i2 = load i8 (%"class.std::__1::ctype"*, i8)*, i8 (%"class.std::__1::ctype"*, i8)** %vfn, align 8
  %call = call signext i8 %i2(%"class.std::__1::ctype"* %this1, i8 signext %i)
  ret i8 %call
}

; Function Attrs: nounwind
declare %"class.std::__1::locale"* @_ZNSt3__16localeD1Ev(%"class.std::__1::locale"* returned) unnamed_addr #10

declare %"class.std::__1::locale::facet"* @_ZNKSt3__16locale9use_facetERNS0_2idE(%"class.std::__1::locale"*, %"class.std::__1::locale::id"* nonnull align 8 dereferenceable(12)) #4

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__18ios_base8setstateEj(%"class.std::__1::ios_base"* %this, i32 %__state) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::ios_base"*, align 8
  %__state.addr = alloca i32, align 4
  store %"class.std::__1::ios_base"* %this, %"class.std::__1::ios_base"** %this.addr, align 8
  store i32 %__state, i32* %__state.addr, align 4
  %this1 = load %"class.std::__1::ios_base"*, %"class.std::__1::ios_base"** %this.addr, align 8
  %__rdstate_ = getelementptr inbounds %"class.std::__1::ios_base", %"class.std::__1::ios_base"* %this1, i32 0, i32 4
  %i = load i32, i32* %__rdstate_, align 8
  %i1 = load i32, i32* %__state.addr, align 4
  %or = or i32 %i, %i1
  call void @_ZNSt3__18ios_base5clearEj(%"class.std::__1::ios_base"* %this1, i32 %or)
  ret void
}

declare void @_ZNSt3__18ios_base5clearEj(%"class.std::__1::ios_base"*, i32) #4

; Function Attrs: nounwind
declare i64 @strlen(i8*) #10

declare nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE3putEc(%"class.std::__1::basic_ostream"*, i8 signext) #4

declare nonnull align 8 dereferenceable(8) %"class.std::__1::basic_ostream"* @_ZNSt3__113basic_ostreamIcNS_11char_traitsIcEEE5flushEv(%"class.std::__1::basic_ostream"*) #4

attributes #0 = { noinline optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline norecurse optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind willreturn }
attributes #4 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { argmemonly nounwind willreturn writeonly }
attributes #7 = { noinline noreturn nounwind }
attributes #8 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { noinline noreturn optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #10 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #11 = { nounwind willreturn }
attributes #12 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #13 = { builtin allocsize(0) }
attributes #14 = { nounwind }
attributes #15 = { noreturn nounwind }
attributes #16 = { noreturn }
attributes #17 = { builtin nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
