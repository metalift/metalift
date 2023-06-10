; ModuleID = 'tuples2.ll'
source_filename = "tuples2.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%struct.tup = type { %"class.std::__1::tuple" }
%"class.std::__1::tuple" = type { %"struct.std::__1::__tuple_impl" }
%"struct.std::__1::__tuple_impl" = type { %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf.0" }
%"class.std::__1::__tuple_leaf" = type { i32 }
%"class.std::__1::__tuple_leaf.0" = type { i32 }
%"struct.std::__1::__tuple_indices" = type { i8 }
%"struct.std::__1::__tuple_types" = type { i8 }
%"struct.std::__1::__tuple_indices.1" = type { i8 }
%"struct.std::__1::__tuple_types.2" = type { i8 }

; Function Attrs: noinline optnone ssp uwtable
define i32 @_Z4testii(i32 %arg, i32 %arg1) #0 {
bb:
  %i = alloca i32, align 4
  %i2 = alloca i32, align 4
  %i3 = alloca %struct.tup*, align 8
  %i4 = alloca %struct.tup*, align 8
  %i5 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i2, align 4
  %i6 = load i32, i32* %i, align 4
  %i7 = load i32, i32* %i, align 4
  %i8 = call %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %i6, i32 %i7)
  store %struct.tup* %i8, %struct.tup** %i3, align 8
  %i9 = load i32, i32* %i2, align 4
  %i10 = load i32, i32* %i2, align 4
  %i11 = call %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %i9, i32 %i10)
  store %struct.tup* %i11, %struct.tup** %i4, align 8
  %i12 = load %struct.tup*, %struct.tup** %i3, align 8
  %i13 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i12, i32 0)
  %i14 = load %struct.tup*, %struct.tup** %i3, align 8
  %i15 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i14, i32 1)
  %i16 = add nsw i32 %i13, %i15
  %i17 = load %struct.tup*, %struct.tup** %i4, align 8
  %i18 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i17, i32 0)
  %i19 = add nsw i32 %i16, %i18
  %i20 = load %struct.tup*, %struct.tup** %i4, align 8
  %i21 = call i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %i20, i32 1)
  %i22 = add nsw i32 %i19, %i21
  store i32 %i22, i32* %i5, align 4
  %i23 = load i32, i32* %i5, align 4
  ret i32 %i23
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr %struct.tup* @_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_(i32 %arg, i32 %arg1) #0 {
bb:
  %i = alloca i32, align 4
  %i2 = alloca i32, align 4
  %i3 = alloca %struct.tup*, align 8
  %i4 = alloca %"class.std::__1::tuple", align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i2, align 4
  %i5 = call %struct.tup* @_Z8newTupleIJiiEEP3tupIJDpT_EEv()
  store %struct.tup* %i5, %struct.tup** %i3, align 8
  %i6 = call i64 @_ZNSt3__110make_tupleIJRiS1_EEENS_5tupleIJDpNS_18__unwrap_ref_decayIT_E4typeEEEEDpOS4_(i32* nonnull align 4 dereferenceable(4) %i, i32* nonnull align 4 dereferenceable(4) %i2)
  %i7 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i4, i32 0, i32 0
  %i8 = bitcast %"struct.std::__1::__tuple_impl"* %i7 to i64*
  store i64 %i6, i64* %i8, align 4
  %i9 = load %struct.tup*, %struct.tup** %i3, align 8
  %i10 = getelementptr inbounds %struct.tup, %struct.tup* %i9, i32 0, i32 0
  %i11 = call nonnull align 4 dereferenceable(8) %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEaSEOS1_(%"class.std::__1::tuple"* %i10, %"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %i4) #4
  %i12 = load %struct.tup*, %struct.tup** %i3, align 8
  ret %struct.tup* %i12
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi(%struct.tup* %arg, i32 %arg1) #1 {
bb:
  %i = alloca %struct.tup*, align 8
  %i2 = alloca i32, align 4
  store %struct.tup* %arg, %struct.tup** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i3 = load %struct.tup*, %struct.tup** %i, align 8
  %i4 = getelementptr inbounds %struct.tup, %struct.tup* %i3, i32 0, i32 0
  %i5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__13getILm0EJiiEEERNS_13tuple_elementIXT_ENS_5tupleIJDpT0_EEEE4typeERS5_(%"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %i4) #4
  %i6 = load i32, i32* %i5, align 4
  ret i32 %i6
}

; Function Attrs: noinline optnone ssp uwtable
define linkonce_odr %struct.tup* @_Z8newTupleIJiiEEP3tupIJDpT_EEv() #0 {
bb:
  %i = call noalias nonnull i8* @_Znwm(i64 8) #5
  %i1 = bitcast i8* %i to %struct.tup*
  %i2 = bitcast %struct.tup* %i1 to i8*
  call void @llvm.memset.p0i8.i64(i8* align 8 %i2, i8 0, i64 8, i1 false)
  call void @_ZN3tupIJiiEEC1Ev(%struct.tup* %i1) #4
  ret %struct.tup* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNSt3__110make_tupleIJRiS1_EEENS_5tupleIJDpNS_18__unwrap_ref_decayIT_E4typeEEEEDpOS4_(i32* nonnull align 4 dereferenceable(4) %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #1 {
bb:
  %i = alloca %"class.std::__1::tuple", align 4
  %i2 = alloca i32*, align 8
  %i3 = alloca i32*, align 8
  store i32* %arg, i32** %i2, align 8
  store i32* %arg1, i32** %i3, align 8
  %i4 = load i32*, i32** %i2, align 8
  %i5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i4) #4
  %i6 = load i32*, i32** %i3, align 8
  %i7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i6) #4
  call void @_ZNSt3__15tupleIJiiEEC1IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %i, i32* nonnull align 4 dereferenceable(4) %i5, i32* nonnull align 4 dereferenceable(4) %i7) #4
  %i8 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i, i32 0, i32 0
  %i9 = bitcast %"struct.std::__1::__tuple_impl"* %i8 to i64*
  %i10 = load i64, i64* %i9, align 4
  ret i64 %i10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %"class.std::__1::tuple"* @_ZNSt3__15tupleIJiiEEaSEOS1_(%"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %arg1) #1 align 2 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  %i2 = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  store %"class.std::__1::tuple"* %arg1, %"class.std::__1::tuple"** %i2, align 8
  %i3 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  %i4 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i3, i32 0, i32 0
  %i5 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i2, align 8
  %i6 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i5, i32 0, i32 0
  %i7 = call nonnull align 4 dereferenceable(8) %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEaSEOS3_(%"struct.std::__1::__tuple_impl"* %i4, %"struct.std::__1::__tuple_impl"* nonnull align 4 dereferenceable(8) %i6) #4
  ret %"class.std::__1::tuple"* %i3
}

; Function Attrs: nobuiltin allocsize(0)
declare nonnull i8* @_Znwm(i64) #2

; Function Attrs: argmemonly nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #3

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZN3tupIJiiEEC1Ev(%struct.tup* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %struct.tup*, align 8
  store %struct.tup* %arg, %struct.tup** %i, align 8
  %i1 = load %struct.tup*, %struct.tup** %i, align 8
  call void @_ZN3tupIJiiEEC2Ev(%struct.tup* %i1) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZN3tupIJiiEEC2Ev(%struct.tup* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %struct.tup*, align 8
  store %struct.tup* %arg, %struct.tup** %i, align 8
  %i1 = load %struct.tup*, %struct.tup** %i, align 8
  %i2 = getelementptr inbounds %struct.tup, %struct.tup* %i1, i32 0, i32 0
  call void @_ZNSt3__15tupleIJiiEEC1ILb1ELPv0EEEv(%"class.std::__1::tuple"* %i2) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC1ILb1ELPv0EEEv(%"class.std::__1::tuple"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  %i1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  call void @_ZNSt3__15tupleIJiiEEC2ILb1ELPv0EEEv(%"class.std::__1::tuple"* %i1) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC2ILb1ELPv0EEEv(%"class.std::__1::tuple"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  %i1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i1, i32 0, i32 0
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1Ev(%"struct.std::__1::__tuple_impl"* %i2) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1Ev(%"struct.std::__1::__tuple_impl"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"** %i, align 8
  %i1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i, align 8
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2Ev(%"struct.std::__1::__tuple_impl"* %i1) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2Ev(%"struct.std::__1::__tuple_impl"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"** %i, align 8
  %i1 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i, align 8
  %i2 = bitcast %"struct.std::__1::__tuple_impl"* %i1 to %"class.std::__1::__tuple_leaf"*
  call void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf"* %i2) #4
  %i3 = bitcast %"struct.std::__1::__tuple_impl"* %i1 to i8*
  %i4 = getelementptr inbounds i8, i8* %i3, i64 4
  %i5 = bitcast i8* %i4 to %"class.std::__1::__tuple_leaf.0"*
  call void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf.0"* %i5) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf"*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %i1, i32 0, i32 0
  store i32 0, i32* %i2, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2Ev(%"class.std::__1::__tuple_leaf.0"* %arg) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %i1, i32 0, i32 0
  store i32 0, i32* %i2, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %arg) #1 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC1IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i5 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  %i6 = load i32*, i32** %i3, align 8
  %i7 = load i32*, i32** %i4, align 8
  call void @_ZNSt3__15tupleIJiiEEC2IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %i5, i32* nonnull align 4 dereferenceable(4) %i6, i32* nonnull align 4 dereferenceable(4) %i7) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__15tupleIJiiEEC2IJRiS3_ELb0ELb0EEEDpOT_(%"class.std::__1::tuple"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  %i3 = alloca i32*, align 8
  %i4 = alloca i32*, align 8
  %i5 = alloca %"struct.std::__1::__tuple_indices", align 1
  %i6 = alloca %"struct.std::__1::__tuple_types", align 1
  %i7 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %i8 = alloca %"struct.std::__1::__tuple_types.2", align 1
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  store i32* %arg1, i32** %i3, align 8
  store i32* %arg2, i32** %i4, align 8
  %i9 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  %i10 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i9, i32 0, i32 0
  %i11 = load i32*, i32** %i3, align 8
  %i12 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i11) #4
  %i13 = load i32*, i32** %i4, align 8
  %i14 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i13) #4
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %i10, i32* nonnull align 4 dereferenceable(4) %i12, i32* nonnull align 4 dereferenceable(4) %i14) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC1IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types", align 1
  %i4 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %i5 = alloca %"struct.std::__1::__tuple_types.2", align 1
  %i6 = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %i7 = alloca i32*, align 8
  %i8 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"** %i6, align 8
  store i32* %arg1, i32** %i7, align 8
  store i32* %arg2, i32** %i8, align 8
  %i9 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i6, align 8
  %i10 = load i32*, i32** %i7, align 8
  %i11 = load i32*, i32** %i8, align 8
  call void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %i9, i32* nonnull align 4 dereferenceable(4) %i10, i32* nonnull align 4 dereferenceable(4) %i11) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEC2IJLm0ELm1EEJiiEJEJEJRiS5_EEENS1_IJXspT_EEEENS_13__tuple_typesIJDpT0_EEENS1_IJXspT1_EEEENS7_IJDpT2_EEEDpOT3_(%"struct.std::__1::__tuple_impl"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1, i32* nonnull align 4 dereferenceable(4) %arg2) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"struct.std::__1::__tuple_indices", align 1
  %i3 = alloca %"struct.std::__1::__tuple_types", align 1
  %i4 = alloca %"struct.std::__1::__tuple_indices.1", align 1
  %i5 = alloca %"struct.std::__1::__tuple_types.2", align 1
  %i6 = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %i7 = alloca i32*, align 8
  %i8 = alloca i32*, align 8
  store %"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"** %i6, align 8
  store i32* %arg1, i32** %i7, align 8
  store i32* %arg2, i32** %i8, align 8
  %i9 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i6, align 8
  %i10 = bitcast %"struct.std::__1::__tuple_impl"* %i9 to %"class.std::__1::__tuple_leaf"*
  %i11 = load i32*, i32** %i7, align 8
  %i12 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i11) #4
  call void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf"* %i10, i32* nonnull align 4 dereferenceable(4) %i12) #4
  %i13 = bitcast %"struct.std::__1::__tuple_impl"* %i9 to i8*
  %i14 = getelementptr inbounds i8, i8* %i13, i64 4
  %i15 = bitcast i8* %i14 to %"class.std::__1::__tuple_leaf.0"*
  %i16 = load i32*, i32** %i8, align 8
  %i17 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i16) #4
  call void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf.0"* %i15, i32* nonnull align 4 dereferenceable(4) %i17) #4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_leafILm0EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i4 = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %i3, i32 0, i32 0
  %i5 = load i32*, i32** %i2, align 8
  %i6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i5) #4
  %i7 = load i32, i32* %i6, align 4
  store i32 %i7, i32* %i4, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr void @_ZNSt3__112__tuple_leafILm1EiLb0EEC2IRivEEOT_(%"class.std::__1::__tuple_leaf.0"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) unnamed_addr #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i4 = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %i3, i32 0, i32 0
  %i5 = load i32*, i32** %i2, align 8
  %i6 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIRiEEOT_RNS_16remove_referenceIS2_E4typeE(i32* nonnull align 4 dereferenceable(4) %i5) #4
  %i7 = load i32, i32* %i6, align 4
  store i32 %i7, i32* %i4, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(8) %"struct.std::__1::__tuple_impl"* @_ZNSt3__112__tuple_implINS_15__tuple_indicesIJLm0ELm1EEEEJiiEEaSEOS3_(%"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"* nonnull align 4 dereferenceable(8) %arg1) #1 align 2 {
bb:
  %i = alloca %"struct.std::__1::__tuple_impl"*, align 8
  %i2 = alloca %"struct.std::__1::__tuple_impl"*, align 8
  store %"struct.std::__1::__tuple_impl"* %arg, %"struct.std::__1::__tuple_impl"** %i, align 8
  store %"struct.std::__1::__tuple_impl"* %arg1, %"struct.std::__1::__tuple_impl"** %i2, align 8
  %i3 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i, align 8
  %i4 = bitcast %"struct.std::__1::__tuple_impl"* %i3 to %"class.std::__1::__tuple_leaf"*
  %i5 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i2, align 8
  %i6 = bitcast %"struct.std::__1::__tuple_impl"* %i5 to %"class.std::__1::__tuple_leaf"*
  %i7 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %i6) #4
  %i8 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i7) #4
  %i9 = call nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf"* %i4, i32* nonnull align 4 dereferenceable(4) %i8) #4
  %i10 = bitcast %"struct.std::__1::__tuple_impl"* %i3 to i8*
  %i11 = getelementptr inbounds i8, i8* %i10, i64 4
  %i12 = bitcast i8* %i11 to %"class.std::__1::__tuple_leaf.0"*
  %i13 = load %"struct.std::__1::__tuple_impl"*, %"struct.std::__1::__tuple_impl"** %i2, align 8
  %i14 = bitcast %"struct.std::__1::__tuple_impl"* %i13 to i8*
  %i15 = getelementptr inbounds i8, i8* %i14, i64 4
  %i16 = bitcast i8* %i15 to %"class.std::__1::__tuple_leaf.0"*
  %i17 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm1EiLb0EE3getEv(%"class.std::__1::__tuple_leaf.0"* %i16) #4
  %i18 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i17) #4
  %i19 = call nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf.0"* %i12, i32* nonnull align 4 dereferenceable(4) %i18) #4
  call void @_ZNSt3__19__swallowIJRNS_12__tuple_leafILm0EiLb0EEERNS1_ILm1EiLb0EEEEEEvDpOT_(%"class.std::__1::__tuple_leaf"* nonnull align 4 dereferenceable(4) %i9, %"class.std::__1::__tuple_leaf.0"* nonnull align 4 dereferenceable(4) %i19) #4
  ret %"struct.std::__1::__tuple_impl"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden void @_ZNSt3__19__swallowIJRNS_12__tuple_leafILm0EiLb0EEERNS1_ILm1EiLb0EEEEEEvDpOT_(%"class.std::__1::__tuple_leaf"* nonnull align 4 dereferenceable(4) %arg, %"class.std::__1::__tuple_leaf.0"* nonnull align 4 dereferenceable(4) %arg1) #1 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %i2 = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %i, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg1, %"class.std::__1::__tuple_leaf.0"** %i2, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf"* @_ZNSt3__112__tuple_leafILm0EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i4 = load i32*, i32** %i2, align 8
  %i5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i4) #4
  %i6 = load i32, i32* %i5, align 4
  %i7 = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %i3, i32 0, i32 0
  store i32 %i6, i32* %i7, align 4
  ret %"class.std::__1::__tuple_leaf"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %arg) #1 {
bb:
  %i = alloca i32*, align 8
  store i32* %arg, i32** %i, align 8
  %i1 = load i32*, i32** %i, align 8
  ret i32* %i1
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %arg) #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf"*, align 8
  store %"class.std::__1::__tuple_leaf"* %arg, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i1 = load %"class.std::__1::__tuple_leaf"*, %"class.std::__1::__tuple_leaf"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__tuple_leaf", %"class.std::__1::__tuple_leaf"* %i1, i32 0, i32 0
  ret i32* %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr nonnull align 4 dereferenceable(4) %"class.std::__1::__tuple_leaf.0"* @_ZNSt3__112__tuple_leafILm1EiLb0EEaSIiEERS1_OT_(%"class.std::__1::__tuple_leaf.0"* %arg, i32* nonnull align 4 dereferenceable(4) %arg1) #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  %i2 = alloca i32*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  store i32* %arg1, i32** %i2, align 8
  %i3 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i4 = load i32*, i32** %i2, align 8
  %i5 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__17forwardIiEEOT_RNS_16remove_referenceIS1_E4typeE(i32* nonnull align 4 dereferenceable(4) %i4) #4
  %i6 = load i32, i32* %i5, align 4
  %i7 = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %i3, i32 0, i32 0
  store i32 %i6, i32* %i7, align 4
  ret %"class.std::__1::__tuple_leaf.0"* %i3
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm1EiLb0EE3getEv(%"class.std::__1::__tuple_leaf.0"* %arg) #1 align 2 {
bb:
  %i = alloca %"class.std::__1::__tuple_leaf.0"*, align 8
  store %"class.std::__1::__tuple_leaf.0"* %arg, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i1 = load %"class.std::__1::__tuple_leaf.0"*, %"class.std::__1::__tuple_leaf.0"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::__tuple_leaf.0", %"class.std::__1::__tuple_leaf.0"* %i1, i32 0, i32 0
  ret i32* %i2
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__13getILm0EJiiEEERNS_13tuple_elementIXT_ENS_5tupleIJDpT0_EEEE4typeERS5_(%"class.std::__1::tuple"* nonnull align 4 dereferenceable(8) %arg) #1 {
bb:
  %i = alloca %"class.std::__1::tuple"*, align 8
  store %"class.std::__1::tuple"* %arg, %"class.std::__1::tuple"** %i, align 8
  %i1 = load %"class.std::__1::tuple"*, %"class.std::__1::tuple"** %i, align 8
  %i2 = getelementptr inbounds %"class.std::__1::tuple", %"class.std::__1::tuple"* %i1, i32 0, i32 0
  %i3 = bitcast %"struct.std::__1::__tuple_impl"* %i2 to %"class.std::__1::__tuple_leaf"*
  %i4 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__112__tuple_leafILm0EiLb0EE3getEv(%"class.std::__1::__tuple_leaf"* %i3) #4
  ret i32* %i4
}

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nobuiltin allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind willreturn writeonly }
attributes #4 = { nounwind }
attributes #5 = { builtin allocsize(0) }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
