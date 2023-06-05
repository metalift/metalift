; ModuleID = 'casper/arithmetic/ConditionalCount.ll'
source_filename = "casper/arithmetic/ConditionalCount.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

%struct.list = type { %"class.std::__1::vector" }
%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }

; Function Attrs: noinline optnone ssp uwtable
define i32 @_Z4testP4listIiE(%struct.list* %arg) #0 {
bb:
  %tmp = alloca %struct.list*, align 8
  %tmp1 = alloca i32, align 4
  %tmp2 = alloca i32, align 4
  %tmp3 = alloca i32, align 4
  store %struct.list* %arg, %struct.list** %tmp, align 8
  store i32 0, i32* %tmp1, align 4
  store i32 0, i32* %tmp2, align 4
  br label %bb4

bb4:                                              ; preds = %bb19, %bb
  %tmp5 = load i32, i32* %tmp2, align 4
  %tmp6 = load %struct.list*, %struct.list** %tmp, align 8
  %tmp7 = call i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %tmp6)
  %tmp8 = icmp slt i32 %tmp5, %tmp7
  br i1 %tmp8, label %bb24, label %bb25

bb9:                                              ; preds = %bb24
  %tmp10 = load %struct.list*, %struct.list** %tmp, align 8
  %tmp11 = load i32, i32* %tmp2, align 4
  %tmp12 = call i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %tmp10, i32 %tmp11)
  store i32 %tmp12, i32* %tmp3, align 4
  %tmp13 = load i32, i32* %tmp3, align 4
  %tmp14 = icmp slt i32 %tmp13, 100
  br i1 %tmp14, label %bb26, label %bb27

bb15:                                             ; preds = %bb26
  %tmp16 = load i32, i32* %tmp1, align 4
  %tmp17 = add nsw i32 %tmp16, 1
  store i32 %tmp17, i32* %tmp1, align 4
  br label %bb18

bb18:                                             ; preds = %bb27, %bb15
  br label %bb19

bb19:                                             ; preds = %bb18
  %tmp20 = load i32, i32* %tmp2, align 4
  %tmp21 = add nsw i32 %tmp20, 1
  store i32 %tmp21, i32* %tmp2, align 4
  br label %bb4

bb22:                                             ; preds = %bb25
  %tmp23 = load i32, i32* %tmp1, align 4
  ret i32 %tmp23

bb24:                                             ; preds = %bb4
  br label %bb9

bb25:                                             ; preds = %bb4
  br label %bb22

bb26:                                             ; preds = %bb9
  br label %bb15

bb27:                                             ; preds = %bb9
  br label %bb18
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %arg) #1 {
bb:
  %tmp = alloca %struct.list*, align 8
  store %struct.list* %arg, %struct.list** %tmp, align 8
  %tmp1 = load %struct.list*, %struct.list** %tmp, align 8
  %tmp2 = getelementptr inbounds %struct.list, %struct.list* %tmp1, i32 0, i32 0
  %tmp3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %tmp2) #2
  %tmp4 = trunc i64 %tmp3 to i32
  ret i32 %tmp4
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %arg, i32 %arg1) #1 {
bb:
  %tmp = alloca %struct.list*, align 8
  %tmp2 = alloca i32, align 4
  store %struct.list* %arg, %struct.list** %tmp, align 8
  store i32 %arg1, i32* %tmp2, align 4
  %tmp3 = load %struct.list*, %struct.list** %tmp, align 8
  %tmp4 = getelementptr inbounds %struct.list, %struct.list* %tmp3, i32 0, i32 0
  %tmp5 = load i32, i32* %tmp2, align 4
  %tmp6 = sext i32 %tmp5 to i64
  %tmp7 = call dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %tmp4, i64 %tmp6) #2
  %tmp8 = load i32, i32* %tmp7, align 4
  ret i32 %tmp8
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %arg) #1 align 2 {
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

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %arg, i64 %arg1) #1 align 2 {
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

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 10.0.0 "}
