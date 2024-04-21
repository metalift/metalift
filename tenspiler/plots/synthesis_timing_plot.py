import csv

import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np

blend_test_name = [
    "normal_blend_f",
    "normal_blend_8",
    "dissolve_blend_8",
    "darken_blend_8",
    "multiply_blend_8",
    "linear_burn_8",
    "color_burn_8",
    "lighten_blend_8",
    "screen_blend_8",
    "linear_dodge_8",
    "color_dodge_8",
    "overlay_blend_8",
]
llama_test_name = [
    "transformer_part4",
    "matmul",
    "transformer_part1",
    "transformer_part2",
    "rmsnorm_part1",
    "rmsnorm_part2",
    "transformer_part3",
    "softmax_part1",
    "softmax_part2",
    "softmax_part3",
    "softmax_part4",
]
blas_test_name = ["dot", "gemv"]
darknet_test_name = [
    "matrix_add_matrix",
    "mag_array",
    "mse_array",
    "mult_add_into_cpu",
    "ol_l2_cpu1",
    "ol_l2_cpu2",
    "scale_array",
    "scale_matrix",
    "sum_array",
    "translate_array",
]
dsp_test_name = [
    "matadd",
    "matscal",
    "matsub",
    "vadd",
    "vcopy",
    "vmul",
    "vneg",
    "voffset",
    "vrecip",
    "vscal",
    "vsub",
    "wvec",
]
dspstone_test_name = ["mat1x3", "n_real_updates"]
makespeare_test_name = ["sum_of_squares"]
mathfu_test_name = [
    "diveq_sca",
    "diveq",
    "len_sq",
    "len",
    "matmul_sca",
    "muleq_sca",
    "muleq",
    "negate",
    "pluseq",
    "subeq_sca",
    "subeq",
]
simpl_array_test_name = [
    "array_inc",
    "array_sum",
    "cube_in_place",
    "fourth_in_place",
    "sum_elts",
]
utdsp_test_name = ["fir_small", "lmsfir1", "lmsfir2"]

blend_test_name = sorted(blend_test_name)
llama_test_name = sorted(llama_test_name)
blas_test_name = sorted(blas_test_name)
darknet_test_name = sorted(darknet_test_name)
dsp_test_name = sorted(dsp_test_name)
dspstone_test_name = sorted(dspstone_test_name)
makespeare_test_name = sorted(makespeare_test_name)
mathfu_test_name = sorted(mathfu_test_name)
simpl_array_test_name = sorted(simpl_array_test_name)
utdsp_test_name = sorted(utdsp_test_name)

plt.rcParams.update({"font.size": 12})

suite_name_to_benchmarks = {
    "blend": blend_test_name,
    "llama": llama_test_name,
    "blas": blas_test_name,
    "darknet": darknet_test_name,
    "utdsp": utdsp_test_name,
    "dsp": dsp_test_name,
    "dspstone": dspstone_test_name,
    "makespeare": makespeare_test_name,
    "mathfu": mathfu_test_name,
    "simpl_array": simpl_array_test_name,
}


def process_tsv(file_path):
    holing_col, general_col = -3, -4
    results = {}

    with open(file_path, newline="") as tsvfile:
        reader = csv.reader(tsvfile, delimiter="\t")
        # Skip first row
        next(reader, None)
        # last two columns of each row are 'holing time total' and 'general timing total'
        for row in reader:
            if row[0] == "" or row[holing_col] == "" or row[general_col] == "":
                continue
            results[row[0]] = [
                float(row[holing_col]),
                float(row[general_col]) if row[general_col] != "timeout" else -1,
            ]

    return results


def plot_synthesis_data(data, test_names, title):
    bar_width = 0.5
    spacing = 0.5
    total_width = bar_width + spacing

    # fig = plt.figure(figsize=(20, 5))
    # gs = GridSpec(3, 3, figure=fig)
    # # first line
    # blas_ax = plt.subplot(gs[0, 0])
    # darknet_ax = plt.subplot(gs[0, 1])
    # utdsp_ax = plt.subplot(gs[0, 2])
    # first_line = [(blas_ax, blas_test_name), (darknet_ax, darknet_test_name), (utdsp_ax, utdsp_test_name)]
    # # second line
    # dsp_ax = plt.subplot(gs[1, 0])
    # dspstone_ax = plt.subplot(gs[1, 1])
    # makespeare_ax = plt.subplot(gs[1, 2])
    # second_line = [(dsp_ax, dsp_test_name), (dspstone_ax, dspstone_test_name), (makespeare_ax, makespeare_test_name)]

    # # third line
    # mathfu_ax = plt.subplot(gs[2, 0:2])
    # simpl_array_ax = plt.subplot(gs[2, 2])
    # third_line = [(mathfu_ax, mathfu_test_name), (simpl_array_ax, simpl_array_test_name)]
    for suite_name, test_names in suite_name_to_benchmarks.items():
        fig, ax = plt.subplots()
        c = "#89CFF0"

        x_pos = np.arange(len(test_names)) * total_width

        # fig, ax = plt.subplots()
        for test_name in test_names:
            value = data[test_name][0]
            if value == -1:
                value = 3600
            ax.bar(x_pos[test_names.index(test_name)], value, bar_width, color=c)

        ax.set_ylabel("Synthesis Time (seconds)")
        ax.set_title(suite_name, wrap=True)
        ax.set_xticks(x_pos)

        test_names = [
            t.split("_part")[0] + t.split("_part")[1]
            if t in llama_test_name and len(t.split("_part")) > 1
            else t
            for t in test_names
        ]
        test_names = [
            t[: len(t) - 2]
            if t in blend_test_name and t != "normal_blend_f" and t != "normal_blend_8"
            else t
            for t in test_names
        ]
        # ax.set_xticklabels(test_names, rotation=45, ha="right")

        ax.set_yscale("log")

        ax.axhline(y=3600, color="#4d4c4c", linestyle="--")
        text_x_pos = max(x_pos) + total_width - 0.5
        text_y_pos = 3600 + 50
        plt.text(text_x_pos, text_y_pos, "Timeout", ha="right", va="bottom")

        ax.set_ylim(top=3600 * 2.3)

        # fig.set_size_inches(10, 5)
        fig.set_size_inches(len(test_names) * 1.5, 6)
        # plt.tight_layout()
        plt.savefig(
            f"{suite_name}_synthesis.png", format="png", dpi=300, bbox_inches="tight"
        )


def plot_abolation_data(data):
    bar_width = 0.4
    spacing_between_groups = 0.5
    spacing_within_group = 0

    colors = ["#89CFF0", "#FFD580"]
    bar_labels = ["Opt", "Unopt"]

    group_width = 2 * bar_width + (2 - 1) * spacing_within_group

    for suite_name, test_names in suite_name_to_benchmarks.items():
        x_pos = np.arange(len(test_names)) * (group_width + spacing_between_groups)
        fig, ax = plt.subplots()

        for test_name in test_names:
            values = data[test_name]
            for value_index, value in enumerate(values):
                if value == -1:
                    value = 3600
                adjusted_x_pos = x_pos[test_names.index(test_name)] + (
                    value_index * (bar_width + spacing_within_group)
                )
                ax.bar(adjusted_x_pos, value, bar_width, color=colors[value_index])

        # for key_index, (key, values) in enumerate(data.items()):
        #     if key in test_names:
        #         for value_index, value in enumerate(values):
        #             if value == -1:
        #                 value = 3600
        #             adjusted_x_pos = x_pos[test_names.index(key)] + (value_index * (bar_width + spacing_within_group))
        #             ax.bar(adjusted_x_pos, value, bar_width, color=colors[value_index])

        ax.set_ylabel("Synthesis Time (seconds)", labelpad=15)
        ax.set_title(suite_name)
        ax.set_xticks(x_pos + group_width / 2 - bar_width / 2)

        test_names = [
            t.split("_part")[0] + t.split("_part")[1]
            if t in llama_test_name and len(t.split("_part")) > 1
            else t
            for t in test_names
        ]
        test_names = [
            t[: len(t) - 2]
            if t in blend_test_name and t != "normal_blend_f" and t != "normal_blend_8"
            else t
            for t in test_names
        ]
        labels = list(map(lambda x: str(x), range(len(test_names))))
        print(labels)
        ax.set_xticklabels(labels)

        # Create proxy artists for the legend
        proxies = [
            mpatches.Patch(color=color, label=label)
            for color, label in zip(colors, bar_labels)
        ]
        loc = "upper left"
        if suite_name == "makespeare":
            loc = "best"
        ax.legend(handles=proxies, loc=loc, framealpha=0.3)

        ax.set_yscale("log")
        ax.axhline(y=3600, color="#4d4c4c", linestyle="--")
        text_x_pos = max(x_pos) + group_width - spacing_between_groups
        text_y_pos = 3600 + 50
        plt.text(text_x_pos, text_y_pos, "Timeout", ha="right", va="bottom")

        ax.set_ylim(top=3600 * 2.3)

        # fig.set_size_inches(10, 5)
        fig.set_size_inches(len(test_names) * 1.5, 4)
        plt.savefig(
            f"ablation/{suite_name}_ablation.png",
            format="png",
            dpi=300,
            bbox_inches="tight",
        )


# data = process_tsv("./synth_timings.tsv")
data = process_tsv("./synth_timings.tsv")
plot_abolation_data(data)
# plot_synthesis_data(data, blas_test_name, "BLAS Benchmarks Synthesis Timing")
exit(0)
# plot_synthesis_data(data, blend_test_name, "Blend Benchmarks Synthesis Timing")
# plot_synthesis_data(data, llama_test_name, "Llama Benchmarks Synthesis Timing")
# plot_abolation_data(data, blend_test_name, "Blend Benchmarks Ablation Timing")
# plot_abolation_data(data, llama_test_name, "Llama Benchmarks Ablation Timing")

speedups = []

for test_name in blend_test_name + llama_test_name:
    values = data[test_name]
    holing_time = values[0]
    general_time = values[1]
    if general_time == -1:
        continue
    speedups.append(general_time / holing_time)

print(np.mean(np.array(speedups)))
