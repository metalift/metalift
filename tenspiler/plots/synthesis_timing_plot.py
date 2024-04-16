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

blend_test_name = sorted(blend_test_name)
llama_test_name = sorted(llama_test_name)

plt.rcParams.update({"font.size": 16})


def process_tsv(file_path):
    results = {}

    with open(file_path, newline="") as tsvfile:
        reader = csv.reader(tsvfile, delimiter="\t")
        # Skip first row
        next(reader, None)
        # last two columns of each row are 'holing time total' and 'general timing total'
        for row in reader:
            if row[0] == "" or row[-3] == "" or row[-4] == "":
                continue
            results[row[0]] = [
                float(row[-4]),
                float(row[-3]) if row[-3] != "timeout" else -1,
            ]

    return results


def plot_synthesis_data(data, test_names, title):
    bar_width = 1
    spacing = 0.5
    total_width = bar_width + spacing

    c = "#89CFF0"

    x_pos = np.arange(len(test_names)) * total_width

    fig, ax = plt.subplots()
    for test_name in test_names:
        try:
            value = data[test_name][0]
        except:
            import pdb

            pdb.set_trace()
        if value == -1:
            value = 3600
        ax.bar(x_pos[test_names.index(test_name)], value, bar_width, color=c)

    ax.set_ylabel("Synthesis Time (seconds)")
    ax.set_title(title)
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
    ax.set_xticklabels(test_names, rotation=45, ha="right")

    ax.set_yscale("log")

    ax.axhline(y=3600, color="#4d4c4c", linestyle="--")
    text_x_pos = max(x_pos) + total_width - 0.5
    text_y_pos = 3600 + 50
    plt.text(text_x_pos, text_y_pos, "Timeout", ha="right", va="bottom")

    ax.set_ylim(top=3600 * 2.3)

    fig.set_size_inches(10, 5)
    plt.tight_layout()
    plt.savefig(f"{title}.png", format="png", dpi=300)


def plot_abolation_data(data, test_names, title):
    bar_width = 1
    spacing_between_groups = 0.5
    spacing_within_group = 0

    colors = ["#89CFF0", "#FFD580"]
    bar_labels = ["Opt", "Unopt"]

    group_width = 2 * bar_width + (2 - 1) * spacing_within_group
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

    ax.set_ylabel("Synthesis Time (seconds)")
    ax.set_title(title)
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
    ax.set_xticklabels(test_names, rotation=45, ha="right")

    # Create proxy artists for the legend
    proxies = [
        mpatches.Patch(color=color, label=label)
        for color, label in zip(colors, bar_labels)
    ]
    ax.legend(handles=proxies, loc="upper left", framealpha=0.3)

    ax.set_yscale("log")
    ax.axhline(y=3600, color="#4d4c4c", linestyle="--")
    text_x_pos = max(x_pos) + group_width - spacing_between_groups
    text_y_pos = 3600 + 50
    plt.text(text_x_pos, text_y_pos, "Timeout", ha="right", va="bottom")

    ax.set_ylim(top=3600 * 2.3)

    fig.set_size_inches(10, 5)
    plt.tight_layout()
    plt.savefig(f"{title}.png", format="png", dpi=300)


data = process_tsv("./synth_timings.tsv")

plot_synthesis_data(data, blend_test_name, "Blend Benchmarks Synthesis Timing")
plot_synthesis_data(data, llama_test_name, "Llama Benchmarks Synthesis Timing")
plot_abolation_data(data, blend_test_name, "Blend Benchmarks Ablation Timing")
plot_abolation_data(data, llama_test_name, "Llama Benchmarks Ablation Timing")

speedups = []

for test_name in blend_test_name + llama_test_name:
    values = data[test_name]
    holing_time = values[0]
    general_time = values[1]
    if general_time == -1:
        continue
    speedups.append(general_time / holing_time)

print(np.mean(np.array(speedups)))
