; ModuleID = 'set1.ll'
source_filename = "set1.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

%struct.set = type {}

; Function Attrs: noinline nounwind optnone ssp uwtable
define %struct.set* @test(%struct.set* %arg, i32 %arg1, i32 %arg2) #0 {
bb:
  %i = alloca %struct.set*, align 8
  %i3 = alloca i32, align 4
  %i4 = alloca i32, align 4
  store %struct.set* %arg, %struct.set** %i, align 8
  store i32 %arg1, i32* %i3, align 4
  store i32 %arg2, i32* %i4, align 4
  %i5 = load i32, i32* %i3, align 4
  %i6 = icmp eq i32 %i5, 1
  br i1 %i6, label %bb17, label %bb18

bb7:                                              ; preds = %bb17
  %i8 = load %struct.set*, %struct.set** %i, align 8
  %i9 = load i32, i32* %i4, align 4
  %i10 = call %struct.set* @set_add(%struct.set* %i8, i32 %i9)
  store %struct.set* %i10, %struct.set** %i, align 8
  br label %bb15

bb11:                                             ; preds = %bb18
  %i12 = load %struct.set*, %struct.set** %i, align 8
  %i13 = load i32, i32* %i4, align 4
  %i14 = call %struct.set* @set_remove(%struct.set* %i12, i32 %i13)
  store %struct.set* %i14, %struct.set** %i, align 8
  br label %bb15

bb15:                                             ; preds = %bb11, %bb7
  %i16 = load %struct.set*, %struct.set** %i, align 8
  ret %struct.set* %i16

bb17:                                             ; preds = %bb
  br label %bb7

bb18:                                             ; preds = %bb
  br label %bb11
}

declare %struct.set* @set_add(%struct.set*, i32) #1

declare %struct.set* @set_remove(%struct.set*, i32) #1

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Homebrew clang version 11.1.0"}
