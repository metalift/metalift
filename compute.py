import numpy as np

dissolve_blend_times = [
    49417.10950713605,
    51941.807626746595,
    49152.446375228465,
    50125.028885900974,
    50922.20408376306,
    55325.21975506097,
    55354.91280257702,
    52100.198668427765,
    52763.07985186577,
    55039.514780044556,
]
lighten_blend_times = [
    6495.1019724830985,
    6474.52781139873,
    6498.492977349088,
    6483.102586818859,
    6518.125836271793,
    6471.55554429628,
    6548.087909584865,
    6506.814957363531,
    6428.90987615101,
    6510.439567733556,
]
color_burn_times = [
    6811.4336845465,
    6904.531916370615,
    6893.480039201677,
    6894.629878923297,
    6875.524412840605,
    6860.878876643255,
    6775.848612654954,
    6845.199125818908,
    6833.687928505242,
    6847.875499399379,
]
darken_blend_times = [
    7440.491180401295,
    6960.237090010196,
    7014.856514055282,
    6920.475770253688,
    6555.451127700508,
    6747.862215619534,
    6466.82777418755,
    6595.683592371643,
    6644.421219360083,
    6595.52365122363,
]

print(
    f"dissolve: {np.average(dissolve_blend_times)}ms +/- {np.std(dissolve_blend_times)}ms"
)
print(
    f"lighten: {np.average(lighten_blend_times)}ms +/- {np.std(lighten_blend_times)}ms"
)
print(f"color burn: {np.average(color_burn_times)}ms +/- {np.std(color_burn_times)}ms")
print(f"darken: {np.average(darken_blend_times)}ms +/- {np.std(darken_blend_times)}ms")

silu_times = [
    428388.52825015783,
    433138.83989676833,
    440941.63751322776,
    459931.0295265168,
    460132.5147226453,
    436517.7704282105,
    464577.5275826454,
    466530.069950968,
    468214.98197875917,
    469665.5257474631,
]
rmsnorm_part1_times = [
    119160.69702524692,
    125731.89364094287,
    125708.61126109958,
    126800.67869182676,
    126471.85766045004,
    128912.02453523874,
    130696.13282382488,
    128541.29805509001,
    128821.70819863677,
    128705.66264074296,
]
multiquery_attention_part2_times = [
    1310.9946502372622,
    1224.14315585047,
    1120.775937102735,
    1268.2781917974353,
    1350.0358564779162,
    1221.2453028187156,
    1294.7385916486382,
    1204.417435452342,
    1339.2545711249113,
    1268.318603746593,
]
multiquery_attention_part1_times = [
    947.450845502317,
    691.8289521709085,
    584.223591722548,
    647.9908833280206,
    503.0205212533474,
    481.4839083701372,
    461.70526277273893,
    500.2645459026098,
    406.4097246155143,
    481.5291138365865,
]

print(f"silu: {np.average(silu_times)}ms +/- {np.std(silu_times)}ms")
print(
    f"rmsnorm_part1: {np.average(rmsnorm_part1_times)}ms +/- {np.std(rmsnorm_part1_times)}ms"
)
print(
    f"multiquery attention part 2: {np.average(multiquery_attention_part2_times)}ms +/- {np.std(multiquery_attention_part2_times)}ms"
)
print(
    f"multiquery attention part 1: {np.average(multiquery_attention_part1_times)}ms +/- {np.std(multiquery_attention_part1_times)}ms"
)
