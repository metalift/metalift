; ModuleID = 'while4.ll'
source_filename = "while4.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, i32* %x, align 4
  store i32 1, i32* %y, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %i = load i32, i32* %y, align 4
  %cmp = icmp slt i32 %i, 3
  br i1 %cmp, label %bb, label %bb5

while.body:                                       ; preds = %bb
  %i1 = load i32, i32* %x, align 4
  %i2 = load i32, i32* %y, align 4
  %add = add nsw i32 %i1, %i2
  store i32 %add, i32* %x, align 4
  %i3 = load i32, i32* %y, align 4
  %add1 = add nsw i32 %i3, 1
  store i32 %add1, i32* %y, align 4
  br label %while.cond

while.end:                                        ; preds = %bb5
  %i4 = load i32, i32* %x, align 4
  ret i32 %i4

bb:                                               ; preds = %while.cond
  br label %while.body

bb5:                                              ; preds = %while.cond
  br label %while.end
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
