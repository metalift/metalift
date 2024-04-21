import csv
import re

import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np

blend_test_name = [
    "normal_blend_f",
    "normal_blend_8",
    "dissolve_blend",
    "darken_blend",
    "multiply_blend",
    "linear_burn",
    "color_burn",
    "lighten_blend",
    "screen_blend",
    "linear_dodge",
    "color_dodge",
    "overlay_blend",
]
llama_test_name = [
    "transformer4",
    "matmul",
    "transformer1",
    "transformer2",
    "rmsnorm1",
    "rmsnorm2",
    "transformer3",
    "softmax1",
    "softmax2",
    "softmax3",
    "softmax4",
]
blas_test_name = ["dot", "gemv"]
darknet_test_name = [
    "mag_array",
    "matrix_add_matrix",
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

column_name = [
    "test_name",
    "C++Kernel",
    "C++E2E",
    "C++7BKernel",
    "C++7BE2E",
    "NumPy",
    "MLX",
    "TensorflowKernel",
    "TensorflowE2E",
    "PyTorchKernel",
    "PyTorchE2E",
    "GaudiKernel",
    "GaudiE2E",
    "Gemmini",
    "NP Speedup Kernel",
    "NP Speedup E2E",
    "MLX Speedup Kernel",
    "MLX Speedup E2E",
    "TF Speedup Kernel",
    "TF Speedup E2E",
    "PT Speedup Kernel",
    "PT Speedup E2E",
    "Gaudi Speedup Kernel",
    "Gaudi Speedup E2E",
    "Gemmini Speedup Kernel",
    "Gemmini Speedup E2E",
    "C++GemminiKernel",
    "C++GemminiE2E",
]

blend_start = 0
llama_start = len(blend_test_name)
blas_start = llama_start + len(llama_test_name)
darknet_start = blas_start + len(blas_test_name)
dsp_start = darknet_start + len(darknet_test_name)
dspstone_start = dsp_start + len(dsp_test_name)
makespeare_start = dspstone_start + len(dspstone_test_name)
mathfu_start = makespeare_start + len(makespeare_test_name)
simpl_array_start = mathfu_start + len(mathfu_test_name)
utdsp_start = simpl_array_start + len(simpl_array_test_name)

software = ["NP", "MLX", "TF", "PT"]

hardware = ["Gaudi", "Gemmini"]


def process_csv(file_path):
    number_regex = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?$")
    data = {}
    with open(file_path, newline="") as csvfile:
        reader = csv.reader(csvfile, delimiter=",")
        for row in reader:
            benchmark_name = row[0]
            for i in range(len(row)):
                cell_v = 0
                if i == 0:
                    continue
                value = row[i]
                if bool(number_regex.match(value)):
                    cell_v = float(value)
                data[(benchmark_name, column_name[i])] = cell_v
    return data


# backends = [NP Speedup Kernel] etc
# backend_labels = [NumPy-CPU]
def plot_data(
    data,
    test_names,
    backends,
    backend_labels,
    title,
    number_offset=1.1,
    include_x_axis_legend=False,
    benchmark_start=0,
    title_size=12,
):
    num_keys = len(backend_labels)

    bar_width = 2
    total_width = bar_width * num_keys

    group_spacing = 8
    # backend_label to color
    colors = {
        "TensorFlow-V100": "#4e79a7",
        "TensorFlow-V100 E2E": "#4e79a7",
        "PyTorch-V100": "#f28e2b",
        "PyTorch-V100 E2E": "#f28e2b",
        "MLX-Apple M1": "#e15759",
        "Numpy-CPU": "#76b7b2",
        "TPCC-Gaudi": "#59a14f",
        "TPCC-Gaudi E2E": "#59a14f",
        "PyTorch-Gaudi": "#b07aa1",
        "PyTorch-Gaudi E2E": "#b07aa1",
        "Gemmini": "#edc948",
    }

    # colors = {'TensorFlow-V100': '#4e79a7', 'TensorFlow-V100 E2E': '#A0CBE8',
    #       'PyTorch-V100':'#f28e2b', 'PyTorch-V100 E2E':'#FFBE7D',
    #       'MLX-Apple M1':'#e15759',
    #       'Numpy-CPU': '#76b7b2',
    #       'TPCC-Gaudi':'#59a14f','TPCC-Gaudi E2E':'#8CD17D',
    #       'PyTorch-Gaudi':'#b07aa1','PyTorch-Gaudi E2E':'#D4A6C8',
    #       'Gemmini':'#edc948'}

    fig, ax = plt.subplots()

    speedups_per_backend = {}
    colors_used = {}

    for test_name in test_names:
        for backend in backends:
            print("data", data, test_name, backend)
            value = data[(test_name, backend)]

            group_start = test_names.index(test_name) * (total_width + group_spacing)
            label_index = backends.index(backend)

            position = group_start + label_index * bar_width
            label = backend_labels[label_index]

            if label not in speedups_per_backend:
                speedups_per_backend[label] = []
                colors_used[label] = colors[label]

            speedups_per_backend[label].append(value)
            bar_color = colors[label]
            if "Gaudi" in label and test_name in {"gemv", "vcopy", "mat1x3"}:
                if "E2E" in label:
                    bar_color = colors["PyTorch-Gaudi E2E"]
                else:
                    bar_color = colors["PyTorch-Gaudi"]
            ax.bar(position, value, bar_width, label=label, color=bar_color)

    ax.set_ylabel("Speed Up")
    ax.set_title(title, fontsize=title_size, loc="center")
    ax.set_xticks(
        [
            i * (total_width + group_spacing) + total_width / 2
            for i in range(len(test_names))
        ]
    )

    # ax.set_xticklabels([str(i+1) for i in range(benchmark_start, benchmark_start + len(test_names))])
    ax.set_xticklabels([test_names[i] for i in range(len(test_names))])
    plt.xticks(rotation=45)
    # legend_patches = [mpatches.Patch(color=color, label=label) for label, color in colors_used.items()]
    # ax.legend(handles=legend_patches, loc='upper left', bbox_to_anchor=(1.05, 1), borderaxespad=0.)

    ax.set_yscale("log")

    for label in backend_labels:
        arr = np.array(speedups_per_backend[label])
        arr = arr[arr != 0]

        gmean = np.exp(np.mean(np.log(arr)))

        line = ax.axhline(y=gmean, color=colors[label], linestyle="-")
        right_limit = ax.get_xlim()[1]
        ax.text(
            right_limit,
            gmean * number_offset,
            f"{gmean:.1f}",
            va="center",
            ha="right",
            color=line.get_color(),
        )

    # baseline
    ax.axhline(y=1, color="#4d4c4c", linestyle="--")
    fig.set_size_inches(len(test_names) * 1.2, 5)
    plt.tight_layout()
    plt.savefig(f"./ecoop_plot/{title}.png", format="png", dpi=300)
    # plt.show()

    # Creating and saving the legend separately
    # colors_unique = {'TensorFlow-V100': '#4e79a7',
    #           'PyTorch-V100':'#f28e2b',
    #           'MLX-Apple M1':'#e15759',
    #           'Numpy-CPU': '#76b7b2',
    #           'TPCC-Gaudi':'#59a14f',
    #           'PyTorch-Gaudi':'#b07aa1',
    #           'Gemmini':'#edc948'}
    fig_leg, ax_leg = plt.subplots()
    handles = [
        mpatches.Patch(color=color, label=label) for label, color in colors_used.items()
    ]
    ax_leg.legend(handles=handles, loc="center")
    ax_leg.axis("off")
    fig_leg.canvas.draw()
    bbox = ax_leg.get_window_extent().transformed(fig_leg.dpi_scale_trans.inverted())
    fig_leg.savefig(
        f"./ecoop_plot/{title}-backend-legend.png",
        format="png",
        dpi=300,
        bbox_inches=bbox,
    )
    plt.close(fig_leg)  # Close the legend figure

    # Create and set the custom legend for the x-axis names
    if include_x_axis_legend:
        x_axis_names = test_names
        custom_patches = [
            mpatches.Patch(color="none", label=f"{i+1+benchmark_start}: {name}")
            for i, name in enumerate(x_axis_names)
        ]

        fig_legend, ax_legend = plt.subplots()
        ax_legend.axis("off")  # Turn off the axis
        ax_legend.legend(handles=custom_patches, loc="center")

        fig_legend.set_size_inches(2, 10)  # Adjust size as needed
        plt.savefig(f"./ecoop_plot/{title}-legend.png", format="png", dpi=300)


# convinience:
# backends = [NP Speedup Kernel] etc
# backend_labels = [NumPy-CPU]
# def plot_data(data, test_names, backends, backend_labels, title, number_offset=1.1, include_x_axis_legend=False):
data = process_csv("./timing_data.tsv")  # (benchmark_name, column_name) = value

e2e_backends = [
    "TF Speedup E2E",
    "PT Speedup E2E",
    "MLX Speedup E2E",
    "NP Speedup E2E",
    "Gaudi Speedup E2E",
    "Gemmini Speedup E2E",
]
kernel_backends = [
    "TF Speedup Kernel",
    "PT Speedup Kernel",
    "MLX Speedup Kernel",
    "NP Speedup Kernel",
    "Gaudi Speedup Kernel",
    "Gemmini Speedup Kernel",
]


e2e_backend_labels_blend = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_blend = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    blend_test_name,
    e2e_backends,
    e2e_backend_labels_blend,
    "Blend E2E Performance",
    1.2,
    True,
)
plot_data(
    data,
    blend_test_name,
    kernel_backends,
    kernel_backend_labels_blend,
    "Blend Kernel Performance",
    1.2,
    True,
)


e2e_backend_labels_llama = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "PyTorch-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_llama = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "PyTorch-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    llama_test_name,
    e2e_backends,
    e2e_backend_labels_llama,
    "Llama E2E Performance",
    1.2,
    True,
    llama_start,
)
plot_data(
    data,
    llama_test_name,
    kernel_backends,
    kernel_backend_labels_llama,
    "Llama Kernel Performance",
    1.2,
    True,
    llama_start,
)


e2e_backend_labels_blas = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_blas = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    blas_test_name,
    e2e_backends,
    e2e_backend_labels_blas,
    "blas E2E Performance",
    1.2,
    True,
    blas_start,
)
plot_data(
    data,
    blas_test_name,
    kernel_backends,
    kernel_backend_labels_blas,
    "blas Kernel Performance",
    1.2,
    True,
    blas_start,
)


e2e_backend_labels_darknet = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_darknet = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    darknet_test_name,
    e2e_backends,
    e2e_backend_labels_darknet,
    "darknet E2E Performance",
    1.2,
    True,
    darknet_start,
)
plot_data(
    data,
    darknet_test_name,
    kernel_backends,
    kernel_backend_labels_darknet,
    "darknet Kernel Performance",
    1.2,
    True,
    darknet_start,
)


e2e_backend_labels_dsp = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_dsp = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    dsp_test_name,
    e2e_backends,
    e2e_backend_labels_dsp,
    "DSP E2E Performance",
    1.2,
    True,
    dsp_start,
)
plot_data(
    data,
    dsp_test_name,
    kernel_backends,
    kernel_backend_labels_dsp,
    "DSP Kernel Performance",
    1.2,
    True,
    dsp_start,
)


e2e_backend_labels_dspstone = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_dspstone = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    dspstone_test_name,
    e2e_backends,
    e2e_backend_labels_dspstone,
    "DSPStone E2E Performance",
    1.2,
    True,
    dspstone_start,
    8,
)
plot_data(
    data,
    dspstone_test_name,
    kernel_backends,
    kernel_backend_labels_dspstone,
    "DSPStone Kernel Performance",
    1.2,
    True,
    dspstone_start,
    8,
)


e2e_backend_labels_makespeare = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_makespeare = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    makespeare_test_name,
    e2e_backends,
    e2e_backend_labels_makespeare,
    "makespeare E2E Performance",
    1.2,
    True,
    makespeare_start,
    7,
)
plot_data(
    data,
    makespeare_test_name,
    kernel_backends,
    kernel_backend_labels_makespeare,
    "makespeare Kernel Performance",
    1.2,
    True,
    makespeare_start,
    7,
)


e2e_backend_labels_mathfu = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_mathfu = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    mathfu_test_name,
    e2e_backends,
    e2e_backend_labels_mathfu,
    "mathfu E2E Performance",
    1.2,
    True,
    mathfu_start,
)
plot_data(
    data,
    mathfu_test_name,
    kernel_backends,
    kernel_backend_labels_mathfu,
    "mathfu Kernel Performance",
    1.2,
    True,
    mathfu_start,
)


e2e_backend_labels_simpl_array = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_simpl_array = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    simpl_array_test_name,
    e2e_backends,
    e2e_backend_labels_simpl_array,
    "simpl_array E2E Performance",
    1.2,
    True,
    simpl_array_start,
)
plot_data(
    data,
    simpl_array_test_name,
    kernel_backends,
    kernel_backend_labels_simpl_array,
    "simpl_array Kernel Performance",
    1.2,
    True,
    simpl_array_start,
)


e2e_backend_labels_utdsp = [
    "TensorFlow-V100 E2E",
    "PyTorch-V100 E2E",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi E2E",
    "Gemmini",
]
kernel_backend_labels_utdsp = [
    "TensorFlow-V100",
    "PyTorch-V100",
    "MLX-Apple M1",
    "Numpy-CPU",
    "TPCC-Gaudi",
    "Gemmini",
]
plot_data(
    data,
    utdsp_test_name,
    e2e_backends,
    e2e_backend_labels_utdsp,
    "utdsp E2E Performance",
    1.2,
    True,
    utdsp_start,
)
plot_data(
    data,
    utdsp_test_name,
    kernel_backends,
    kernel_backend_labels_utdsp,
    "utdsp Kernel Performance",
    1.2,
    True,
    utdsp_start,
)


all_speedup = []
all_kernel_speedup = []
all_e2e_speedup = []

all_hw_speedup = []
all_sw_speedup = []

all_hw_kernel_speedup = []
all_sw_kernel_speedup = []

all_hw_e2e_speedup = []
all_sw_e2e_speedup = []

all_test = (
    blend_test_name
    + llama_test_name
    + blas_test_name
    + darknet_test_name
    + dsp_test_name
    + dspstone_test_name
    + makespeare_test_name
    + mathfu_test_name
    + simpl_array_test_name
    + utdsp_test_name
)

for test in all_test:
    for e2e_b in e2e_backends:
        val = data[(test, e2e_b)]
        all_e2e_speedup.append(val)
        if "Gemmini" in e2e_b or "Gaudi" in e2e_b:
            all_hw_speedup.append(val)
            all_hw_e2e_speedup.append(val)
        else:
            all_sw_speedup.append(val)
            all_sw_e2e_speedup.append(val)
        all_speedup.append(val)

    for k_b in kernel_backends:
        val = data[(test, k_b)]
        all_kernel_speedup.append(val)
        if "Gemmini" in k_b or "Gaudi" in k_b:
            all_hw_speedup.append(val)
            all_hw_kernel_speedup.append(val)
        else:
            all_sw_speedup.append(val)
            all_sw_kernel_speedup.append(val)
        all_speedup.append(val)

all_speedup = np.array(all_speedup)
all_kernel_speedup = np.array(all_kernel_speedup)
all_e2e_speedup = np.array(all_e2e_speedup)
all_hw_speedup = np.array(all_hw_speedup)
all_sw_speedup = np.array(all_sw_speedup)
all_hw_kernel_speedup = np.array(all_hw_kernel_speedup)
all_sw_kernel_speedup = np.array(all_sw_kernel_speedup)
all_hw_e2e_speedup = np.array(all_hw_e2e_speedup)
all_sw_e2e_speedup = np.array(all_sw_e2e_speedup)

all_speedup = all_speedup[all_speedup != 0]

all_kernel_speedup = all_kernel_speedup[all_kernel_speedup != 0]
all_e2e_speedup = all_e2e_speedup[all_e2e_speedup != 0]

all_hw_speedup = all_hw_speedup[all_hw_speedup != 0]
all_sw_speedup = all_sw_speedup[all_sw_speedup != 0]

all_hw_kernel_speedup = all_hw_kernel_speedup[all_hw_kernel_speedup != 0]
all_sw_kernel_speedup = all_sw_kernel_speedup[all_sw_kernel_speedup != 0]

all_hw_e2e_speedup = all_hw_e2e_speedup[all_hw_e2e_speedup != 0]
all_sw_e2e_speedup = all_sw_e2e_speedup[all_sw_e2e_speedup != 0]

print(np.mean(all_speedup))

print(np.mean(all_kernel_speedup))
print(np.mean(all_e2e_speedup))

print(np.mean(all_hw_speedup))
print(np.mean(all_sw_speedup))

print(np.mean(all_hw_kernel_speedup))
print(np.mean(all_sw_kernel_speedup))

print(np.mean(all_hw_e2e_speedup))
print(np.mean(all_sw_e2e_speedup))
