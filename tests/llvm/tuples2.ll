; ModuleID = 'tuples2.ll'
source_filename = "tuples2.cc"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

%struct.tup = type { %"class.std::__1::tuple" }
%"class.std::__1::tuple" = type { %"struct.std::__1::__tuple_impl" }
%"struct.std::__1::__tuple_impl" = type { %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf.0" }
%"class.std::__1::__tuple_leaf" = type { i32 }
%"class.std::__1::__tuple_leaf.0" = type { i32 }
%"struct.std::__1::__tuple_indices" = type { i8 }
%"struct.std::__1::__tuple_types" = type { i8 }
%"struct.std::__1::__tuple_indices.1" = type { i8 }
%"struct.std::__1::__tuple_types.2" = type { i8 }

; Function Attrs: noinline optnone sspstrong uwtable
define i32 @_Z4testii(i32 %x, i32 %y) #0 {
entry:
  %x.addr = alloca i32, align 4
  %y.addr = alloca i32, align 4
  %u = alloca %struct.tup*, align 8
  %v = alloca %struct.tup*, align 8
  %z = alloca i32, align 4
  store i32 %x, i32* %x.addr, align 4
  store i32 %y, i32* %y.addr, align 4
  %i = load i32, i32* %x.addr, align 4
  %i1 = load i32, i32* %x.addr, align 4
  %call = call %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %i, i32 %i1)
  store %struct.tup* %call, %struct.tup** %u, align 8
  %i2 = load i32, i32* %y.addr, align 4
  %i3 = load i32, i32* %y.addr, align 4
  %call1 = call %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %i2, i32 %i3)
  store %struct.tup* %call1, %struct.tup** %v, align 8
  %i4 = load %struct.tup*, %struct.tup** %u, align 8
  %call2 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i4, i32 0)
  %i5 = load %struct.tup*, %struct.tup** %u, align 8
  %call3 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i5, i32 1)
  %add = add i32 %call2, %call3
  %i6 = load %struct.tup*, %struct.tup** %v, align 8
  %call4 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i6, i32 0)
  %add5 = add i32 %add, %call4
  %i7 = load %struct.tup*, %struct.tup** %v, align 8
  %call6 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i7, i32 1)
  %add7 = add i32 %add5, %call6
  store i32 %add7, i32* %z, align 4
  %i8 = load i32, i32* %z, align 4
  ret i32 %i8
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %args, i32 %args1) #0 {
entry:
  %args.addr = alloca i32, align 4
  %args.addr2 = alloca i32, align 4
  %r = alloca %struct.tup*, align 8
  %ref.tmp = alloca %"class.std::__1::tuple", align 4
  store i32 %args, i32* %args.addr, align 4
  store i32 %args1, i32* %args.addr2, align 4
  %call = call %struct.tup* @_Z8newTupleIJiiEEP3tupIJDpT_EEv()
  store %struct.tup* %call, %struct.tup** %r, align 8
  %call3 = call i64 @_ZNSt3__110make_tupleIJRiS1_EEENS_5tupleIJDpNS_18__unwrap_ref_decayIT_E4typeEEEEDpOS4_(i32* nonnull align 4 dereferenceable(4) %args.addr, i32* nonnull align 4 dereferenceable(4) %args.addr2)
  %coerce.dive = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %ref.tmp, i32 0, i32 0
  %i = bitcast %"struct.std::__1::__tuple_impl"* %coerce.dive to i64*
  store i64 %call3, i64* %i, align 4
  %i1 = load %struct.tup*, %struct.tup** %r, align 8
  %contents = getelementptr inbounds %struct.tup, %struct.tup* %i1, i32 0, i32 0
  %call4 = call nonnull align 4 dereferenceable(8) %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEaSEOS1_(%"class.std::__1::tuple"* %contents, %"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %ref.tmp) #4
  %i2 = load %struct.tup*, %struct.tup** %r, align 8
  ret %struct.tup* %i2
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %t, i32 %i) #1 {
entry:
  %t.addr = alloca %struct.tup*, align 8
  %i.addr = alloca i32, align 4
  store %struct.tup* %t, %struct.tup** %t.addr, align 8
  store i32 %i, i32* %i.addr, align 4
  %i1 = load %struct.tup*, %struct.tup** %t.addr, align 8
  %contents = getelementptr inbounds %struct.tup, %struct.tup* %i1, i32 0, i32 0
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__13getILm0EJiiEEERNS_13tuple_elementIXT_ENS_5tupleIJDpT0_EEEE4typeERS5_(%"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %contents) #4
  %i2 = load i32, i32* %call, align 4
  ret i32 %i2
}

; Function Attrs: noinline optnone sspstrong uwtable
define linkonce_odr %struct.tup* @_Z8newTupleIJiiEEP3tupIJDpT_EEv() #0 {
entry:
  %call = call noalias nonnull i8* @_Znwm(i64 8) #5
  %i = bitcast i8* %call to %struct.tup*
  %i1 = bitcast %struct.tup* %i to i8*
  call void @llvm.memset.p0i8.i64(i8* align 8 %i1, i8 0, i64 8, i1 false)
  %call1 = call %struct.tup* @_ZN3tupIJiiEEC1Ev(%struct.tup* %i) #4
  ret %struct.tup* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNSt3__110make_tupleIJRiS1_EEENS_5tupleIJDpNS_18__unwrap_ref_decayIT_E4typeEEEEDpOS4_(i32* nonnull align 4 dereferenceable(4) %__t, i32* nonnull align 4 dereferenceable(4) %__t1) #1 {
entry:
  %retval = alloca %"class.std::__1::tuple", align 4
  %__t.addr = alloca i32*, align 8
  %__t.addr2 = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  store i32* %__t1, i32** %__t.addr2, align 8
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32*, i32** %__t.addr2, align 8
  %call3 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i1) #4
  %call4 = call %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC1IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %retval, i32* nonnull align 4 dereferenceable(4) %call, i32* nonnull align 4 dereferenceable(4) %call3) #4
  %coerce.dive = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %retval, i32 0, i32 0
  %i2 = bitcast %"struct.std::__1::__tuple_impl"* %coerce.dive to i64*
  %i3 = load i64, i64* %i2, align 4
  ret i64 %i3
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEaSEOS1_(%"class.std::__1::tuple"* %this, %"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %__t) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  %__t.addr = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  store %"class.std::__1::tuple"* %__t, %"class.std::__1::tuple"** %__t.addr, align 8
  %this1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %__base_ = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %this1, i32 0, i32 0
  %i = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %__t.addr, align 8
  %__base_2 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i, i32 0, i32 0
  %call = call nonnull align 4 dereferenceable(8) %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEaSEOS3_(%"struct.std::__1::__tuple_impl"* %__base_, %"struct.std::__1::__tuple_impl"* nonnull align 4 dereferenceable(8) %__base_2) #4
  ret %"class.std::__1::tuple"* %this1
}

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #2

; Function Attrs: argmemonly nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #3

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.tup* @_ZN3tupIJiiEEC1Ev(%struct.tup* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.tup*, align 8
  store %struct.tup* %this, %struct.tup** %this.addr, align 8
  %this1 = load %struct.tup*, %struct.tup** %this.addr, align 8
  %call = call %struct.tup* @_ZN3tupIJiiEEC2Ev(%struct.tup* %this1) #4
  ret %struct.tup* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %struct.tup* @_ZN3tupIJiiEEC2Ev(%struct.tup* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %struct.tup*, align 8
  store %struct.tup* %this, %struct.tup** %this.addr, align 8
  %this1 = load %struct.tup*, %struct.tup** %this.addr, align 8
  %contents = getelementptr inbounds %struct.tup, %struct.tup* %this1, i32 0, i32 0
  %call = call %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC1ILb1ELPv0EEEv(%"class.std::__1::tuple"* %contents) #4
  ret %struct.tup* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC1ILb1ELPv0EEEv(%"class.std::__1::tuple"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  %this1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %call = call %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC2ILb1ELPv0EEEv(%"class.std::__1::tuple"* %this1) #4
  ret %"class.std::__1::tuple"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC2ILb1ELPv0EEEv(%"class.std::__1::tuple"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  %this1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %__base_ = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %this1, i32 0, i32 0
  %call = call %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1Ev(%"struct.std::__1::__tuple_impl"* %__base_) #4
  ret %"class.std::__1::tuple"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1Ev(%"struct.std::__1::__tuple_impl"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %call = call %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2Ev(%"struct.std::__1::__tuple_impl"* %this1) #4
  ret %"struct.std::__1::__tuple_impl"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2Ev(%"struct.std::__1::__tuple_impl"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %this1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__tuple_impl"* %this1 to %"class.std::__1::__tuple_leaf"*
  %call = call %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf"* %i) #4
  %i1 = bitcast %"struct.std::__1::__tuple_impl"* %this1 to i8*
  %i2 = getelementptr inbounds i8, i8* %i1, i64 4
  %i3 = bitcast i8* %i2 to %"class.std::__1::__tuple_leaf.0"*
  %call2 = call %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf.0"* %i3) #4
  ret %"struct.std::__1::__tuple_impl"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  store %"class.std::__1::__tuple_leaf"* %this, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %this1, i32 0, i32 0
  store i32 0, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf.0"* returned %this) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %this, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %this1, i32 0, i32 0
  store i32 0, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf.0"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %__t) #1 {
entry:
  %__t.addr = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC1IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* returned %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u1) unnamed_addr #1 align 2 {
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
  %call = call %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC2IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %this3, i32* nonnull align 4 dereferenceable(4) %i, i32* nonnull align 4 dereferenceable(4) %i1) #4
  ret %"class.std::__1::tuple"* %this3
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEC2IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* returned %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u1) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::tuple"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr2 = alloca i32*, align 8
  %agg.tmp = alloca %"struct.std::__1::__tuple_indices", align 1
  %agg.tmp4 = alloca %"struct.std::__1::__tuple_types", align 1
  %agg.tmp5 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %agg.tmp6 = alloca %"struct.std::__1::__tuple_types.2", align 1
  store %"class.std::__1::tuple"* %this, %"class.std::__1::tuple"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u1, i32** %__u.addr2, align 8
  %this3 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %this.addr, align 8
  %__base_ = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %this3, i32 0, i32 0
  %i = load i32*, i32** %__u.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32*, i32** %__u.addr2, align 8
  %call7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i1) #4
  %call8 = call %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %__base_, i32* nonnull align 4 dereferenceable(4) %call, i32* nonnull align 4 dereferenceable(4) %call7) #4
  ret %"class.std::__1::tuple"* %this3
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* returned %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u4) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i1 = alloca %"struct.std::__1::__tuple_types", align 1
  %i2 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types.2", align 1
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr5 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u4, i32** %__u.addr5, align 8
  %this6 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i4 = load i32*, i32** %__u.addr, align 8
  %i5 = load i32*, i32** %__u.addr5, align 8
  %call = call %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %this6, i32* nonnull align 4 dereferenceable(4) %i4, i32* nonnull align 4 dereferenceable(4) %i5) #4
  ret %"struct.std::__1::__tuple_impl"* %this6
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* returned %this, i32* nonnull align 4 dereferenceable(4) %__u, i32* nonnull align 4 dereferenceable(4) %__u4) unnamed_addr #1 align 2 {
entry:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i1 = alloca %"struct.std::__1::__tuple_types", align 1
  %i2 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types.2", align 1
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %__u.addr = alloca i32*, align 8
  %__u.addr5 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  store i32* %__u, i32** %__u.addr, align 8
  store i32* %__u4, i32** %__u.addr5, align 8
  %this6 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i4 = bitcast %"struct.std::__1::__tuple_impl"* %this6 to %"class.std::__1::__tuple_leaf"*
  %i5 = load i32*, i32** %__u.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i5) #4
  %call7 = call %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf"* %i4, i32* nonnull align 4 dereferenceable(4) %call) #4
  %i6 = bitcast %"struct.std::__1::__tuple_impl"* %this6 to i8*
  %i7 = getelementptr inbounds i8, i8* %i6, i64 4
  %i8 = bitcast i8* %i7 to %"class.std::__1::__tuple_leaf.0"*
  %i9 = load i32*, i32** %__u.addr5, align 8
  %call8 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i9) #4
  %call9 = call %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf.0"* %i8, i32* nonnull align 4 dereferenceable(4) %call8) #4
  ret %"struct.std::__1::__tuple_impl"* %this6
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf"* returned %this, i32* nonnull align 4 dereferenceable(4) %__t) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf"* %this, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf.0"* returned %this, i32* nonnull align 4 dereferenceable(4) %__t) unnamed_addr #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %this, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %this1, i32 0, i32 0
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf.0"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEaSEOS3_(%"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"* nonnull align 4 dereferenceable(8) %__t) #1 align 2 {
entry:
  %this.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %__t.addr = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %this, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  store %"struct.std::__1::__tuple_impl"* %__t, %"struct.std::__1::__tuple_impl"** %__t.addr, align 8
  %this1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %this.addr, align 8
  %i = bitcast %"struct.std::__1::__tuple_impl"* %this1 to %"class.std::__1::__tuple_leaf"*
  %i1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %__t.addr, align 8
  %i2 = bitcast %"struct.std::__1::__tuple_impl"* %i1 to %"class.std::__1::__tuple_leaf"*
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %i2) #4
  %call2 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %call) #4
  %call3 = call nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf"* %i, i32* nonnull align 4 dereferenceable(4) %call2) #4
  %i3 = bitcast %"struct.std::__1::__tuple_impl"* %this1 to i8*
  %add.ptr = getelementptr inbounds i8, i8* %i3, i64 4
  %i4 = bitcast i8* %add.ptr to %"class.std::__1::__tuple_leaf.0"*
  %i5 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %__t.addr, align 8
  %i6 = bitcast %"struct.std::__1::__tuple_impl"* %i5 to i8*
  %add.ptr4 = getelementptr inbounds i8, i8* %i6, i64 4
  %i7 = bitcast i8* %add.ptr4 to %"class.std::__1::__tuple_leaf.0"*
  %call5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm1EiLb0EE3getEv(%"class.std::__1::__tuple_leaf.0"* %i7) #4
  %call6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %call5) #4
  %call7 = call nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf.0"* %i4, i32* nonnull align 4 dereferenceable(4) %call6) #4
  call void @_ZNSt3__19__swallowIJRNS_12__tuple_leafILm0EiLb0EEERNS1_ILm1EiLb0EEEEEEvDpOT_(%"class.std::__1::__tuple_leaf"* nonnull align 4 dereferenceable(4) %call3, %"class.std::__1::__tuple_leaf.0"* nonnull align 4 dereferenceable(4) %call7) #4
  ret %"struct.std::__1::__tuple_impl"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden void @_ZNSt3__19__swallowIJRNS_12__tuple_leafILm0EiLb0EEERNS1_ILm1EiLb0EEEEEEvDpOT_(%"class.std::__1::__tuple_leaf"* nonnull align 4 dereferenceable(4) %arg, %"class.std::__1::__tuple_leaf.0"* nonnull align 4 dereferenceable(4) %arg1) #1 {
entry:
  %.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %.addr1 = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %.addr, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg1, %"class.std::__1::__tuple_leaf.0"** %.addr1, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf"* %this, i32* nonnull align 4 dereferenceable(4) %__t) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf"* %this, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32, i32* %call, align 4
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %this1, i32 0, i32 0
  store i32 %i1, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %__t) #1 {
entry:
  %__t.addr = alloca i32*, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  ret i32* %i
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf"*, align 8
  store %"class.std::__1::__tuple_leaf"* %this, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %this1, i32 0, i32 0
  ret i32* %__value_
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf.0"* %this, i32* nonnull align 4 dereferenceable(4) %__t) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  %__t.addr = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %this, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  store i32* %__t, i32** %__t.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %i = load i32*, i32** %__t.addr, align 8
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i) #4
  %i1 = load i32, i32* %call, align 4
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %this1, i32 0, i32 0
  store i32 %i1, i32* %__value_, align 4
  ret %"class.std::__1::__tuple_leaf.0"* %this1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm1EiLb0EE3getEv(%"class.std::__1::__tuple_leaf.0"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %this, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %this1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %this.addr, align 8
  %__value_ = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %this1, i32 0, i32 0
  ret i32* %__value_
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__13getILm0EJiiEEERNS_13tuple_elementIXT_ENS_5tupleIJDpT0_EEEE4typeERS5_(%"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %__t) #1 {
entry:
  %__t.addr = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %__t, %"class.std::__1::tuple"** %__t.addr, align 8
  %i = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %__t.addr, align 8
  %__base_ = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i, i32 0, i32 0
  %i1 = bitcast %"struct.std::__1::__tuple_impl"* %__base_ to %"class.std::__1::__tuple_leaf"*
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %i1) #4
  ret i32* %call
}

attributes #0 = { noinline optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind willreturn writeonly }
attributes #4 = { nounwind }
attributes #5 = { builtin allocsize(0) }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
