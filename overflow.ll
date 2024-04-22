; ModuleID = 'overflow.ll'
source_filename = "overflow.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define signext i16 @_Z8overflowss(i16 signext %a, i16 signext %b) #0 {
entry:
  %a.addr = alloca i16, align 2
  %b.addr = alloca i16, align 2
  %c = alloca i16, align 2
  %d = alloca i16, align 2
  %e = alloca i16, align 2
  store i16 %a, i16* %a.addr, align 2
  store i16 %b, i16* %b.addr, align 2
  %i = load i16, i16* %a.addr, align 2
  %conv = sext i16 %i to i32
  %i1 = load i16, i16* %b.addr, align 2
  %conv1 = sext i16 %i1 to i32
  %mul = mul nsw i32 %conv, %conv1
  %conv2 = trunc i32 %mul to i16
  store i16 %conv2, i16* %c, align 2
  store i16 250, i16* %d, align 2
  %i2 = load i16, i16* %c, align 2
  %conv3 = sext i16 %i2 to i32
  %i3 = load i16, i16* %d, align 2
  %conv4 = sext i16 %i3 to i32
  %mul5 = mul nsw i32 %conv3, %conv4
  %conv6 = trunc i32 %mul5 to i16
  store i16 %conv6, i16* %e, align 2
  %i4 = load i16, i16* %e, align 2
  ret i16 %i4
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
