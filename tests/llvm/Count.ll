; ModuleID = 'Count.ll'
source_filename = "Count.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%struct.list = type { %"class.std::__1::vector" }
%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }

; Function Attrs: noinline optnone ssp uwtable
define i32 @test(%struct.list* %arg) #0 {
bb:
  %i = alloca %struct.list*, align 8
  %i1 = alloca i32, align 4
  %i2 = alloca i32, align 4
  store %struct.list* %arg, %struct.list** %i, align 8
  store i32 0, i32* %i1, align 4
  store i32 0, i32* %i2, align 4
  br label %bb3

bb3:                                              ; preds = %bb11, %bb
  %i4 = load i32, i32* %i2, align 4
  %i5 = load %struct.list*, %struct.list** %i, align 8
  %i6 = call i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %i5)
  %i7 = icmp slt i32 %i4, %i6
  br i1 %i7, label %bb16, label %bb17

bb8:                                              ; preds = %bb16
  %i9 = load i32, i32* %i1, align 4
  %i10 = add nsw i32 %i9, 1
  store i32 %i10, i32* %i1, align 4
  br label %bb11

bb11:                                             ; preds = %bb8
  %i12 = load i32, i32* %i2, align 4
  %i13 = add nsw i32 %i12, 1
  store i32 %i13, i32* %i2, align 4
  br label %bb3

bb14:                                             ; preds = %bb17
  %i15 = load i32, i32* %i1, align 4
  ret i32 %i15

bb16:                                             ; preds = %bb3
  br label %bb8

bb17:                                             ; preds = %bb3
  br label %bb14
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %arg) #1 {
bb:
  %i = alloca %struct.list*, align 8
  store %struct.list* %arg, %struct.list** %i, align 8
  %i1 = load %struct.list*, %struct.list** %i, align 8
  %i2 = getelementptr inbounds %struct.list, %struct.list* %i1, i32 0, i32 0
  %i3 = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %i2) #2
  %i4 = trunc i64 %i3 to i32
  ret i32 %i4
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %arg) #1 align 2 {
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

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
