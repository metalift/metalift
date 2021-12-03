; ModuleID = 'domino/programs/rcp.ll'
source_filename = "domino/programs/rcp.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

%struct.Packet = type { i32, i32 }

@input_traffic_Bytes = global i32 0, align 4
@sum_rtt_Tr = global i32 0, align 4
@num_pkts_with_rtt = global i32 0, align 4

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @func(i64 %arg) #0 {
bb:
  %i = alloca %struct.Packet, align 4
  %i1 = bitcast %struct.Packet* %i to i64*
  store i64 %arg, i64* %i1, align 4
  %i2 = getelementptr inbounds %struct.Packet, %struct.Packet* %i, i32 0, i32 0
  %i3 = load i32, i32* %i2, align 4
  %i4 = load i32, i32* @input_traffic_Bytes, align 4
  %i5 = add nsw i32 %i4, %i3
  store i32 %i5, i32* @input_traffic_Bytes, align 4
  %i6 = getelementptr inbounds %struct.Packet, %struct.Packet* %i, i32 0, i32 1
  %i7 = load i32, i32* %i6, align 4
  %i8 = icmp slt i32 %i7, 30
  br i1 %i8, label %bb9, label %bb16

bb9:                                              ; preds = %bb
  %i10 = getelementptr inbounds %struct.Packet, %struct.Packet* %i, i32 0, i32 1
  %i11 = load i32, i32* %i10, align 4
  %i12 = load i32, i32* @sum_rtt_Tr, align 4
  %i13 = add nsw i32 %i12, %i11
  store i32 %i13, i32* @sum_rtt_Tr, align 4
  %i14 = load i32, i32* @num_pkts_with_rtt, align 4
  %i15 = add nsw i32 %i14, 1
  store i32 %i15, i32* @num_pkts_with_rtt, align 4
  br label %bb16

bb16:                                             ; preds = %bb9, %bb
  ret void
}

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"Homebrew clang version 13.0.0"}
