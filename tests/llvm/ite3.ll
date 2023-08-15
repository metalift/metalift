; ModuleID = 'ite3.ll'
source_filename = "ite3.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %i) #0 {
entry:
  %i.addr = alloca i32, align 4
  %a = alloca i32, align 4
  store i32 %i, i32* %i.addr, align 4
  store i32 1, i32* %a, align 4
  %i1 = load i32, i32* %i.addr, align 4
  %cmp = icmp sgt i32 %i1, 10
  br i1 %cmp, label %bb, label %bb3

if.then:                                          ; preds = %bb
  store i32 2, i32* %a, align 4
  br label %if.end

if.end:                                           ; preds = %bb3, %if.then
  %i2 = load i32, i32* %a, align 4
  ret i32 %i2

bb:                                               ; preds = %entry
  br label %if.then

bb3:                                              ; preds = %entry
  br label %if.end
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
