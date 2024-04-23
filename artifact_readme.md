Title of the submitted paper: Tenspiler: A Verified Lifting-Based Compiler for Tensor

ECOOP submission number for the paper: 220

# Metadata
**No need to provide them again in the submission**
[comment]TODO: fill this
- OS and resource (CPU, memory, disk, GPU) used by the authors to run the artifact 
    for this do we just include all the config from paper?
- Estimation of the required hardware resources for evaluation. In case the evaluation takes multiple days or requires huge resources, please provide a scaled-down evaluation.
    again do we just cite from paper? We have provided a scaled-down version as described below.
- Known compatibility issues of the container/VM.
- Which badges do you claim for your artifact? Functional? Reusable? Available?
    We claim all three badges.


# Quick-start guide
1. Build the provided Docker container with
```
docker build -t tenspiler .
```
2. Run the container and spawn a shell
```
docker run -v $(pwd):/code/metalift -it tenspiler /bin/bash
```
NOTE: For any `python` command in the Docker environment, please prefix with `poetry run` (as included in all provided commands).

3. To make sure if the synthesis, verification, and code-generation is working, we can perform a quick test of generating the **NumPy** code for the **dot** benchmark.
```
poetry run python tenspiler/generated_code/numpy/generate_numpy_benchmarks.py dot
```
You should find the resulting file at `tenspiler/generated_code/numpy/blas/dot_np.py`.

4. To test if timing scripts are working, we can run one test from each dataset. We first prepare the dataset
```
cp -rfT ./data_sampled/ ./data/
cp -f ./vicuna_weight_sampled.h5 ./vicuna_weight.h5
```
5. We then performce the timing
```
poetry run python tenspiler/benchmarking/numpy_speedup_exec.py dot
poetry run python tenspiler/benchmarking/numpy_speedup_exec.py matmul
```
This should print to the terminal the runtime of the corresponding benchmark in C++ baseline and NumPy as well as the E2E and Kernel speedup.
   
[comment]: do we need the imagenet dataset for running this?
[comment]: yes we need both the ./data_sampled/ and vicuna_weight_sampled.h5 and they need to be renamed properly.


# Overview: What does the artifact comprise?

In this artifact, we include the source code of Tenspiler, the files to obtain results we stated in the paper, and sampled datasets used for evaluation (and script to obtain the full dataset).

Dockerfile: the Dockerfile used to build the environment for evaluation

Source Code and Evaluation Scripts:
- code/metalift/tenspiler/: the folder containing all of Tenspiler
    - benchmarking/: containing the benchmark executables and scripts to obtain speedup of each benchmark on the backend
    - blend/: containing the input code and drivers to synthesis the blend suite
      - cpp/for_synthesis/: the C++ source code used for synthesis
      - general/: the driver files and generated racket file for synthesis without any optimization
      - holing: the driver files and generated racket file for synthesis with all optimizations. Used for synthesis.
    - c2taco/: containing all 8 suites of benchmarks used by C2TACO with same internal structure as blend/
    - llama/: containing the Llama benchmarks
    - codegen/: code-generation scripts from TensIR to each of the 6 backends supported
    - generated_code/: convinient scripts that runs the synthesizer, verifier, and codegen in one run
    - plots/: all data and plots used in paper

[comment]:  we can move the synthesis datasets (llama, c2taco, blend) in this paragraph with 2 sections. benchmarks and evaluation. [comment]: wdym by 'move the datasets in this paragraph with 2 sections'?

Datasets (jpeg and h5): We include `data_sampled/`, `vicuna_weight_sampled.h5`, and `vicuna_weight7b_sampled.h5` as subsamples of the real datasets used for performance evaluation. See the performance secton in Functional badge for more detail. These are located in the /code/metalift/ folder. [comment]TODO: verify this setup and update at all placed.

# Available badge

We offer to publish the artifact on [DARTS](https://drops.dagstuhl.de/opus/institut_darts.php), in which case the available badge will be issued automatically.
If you agree to publishing your artifact under a Creative Commons license, please indicate this here.

We agree to publish the artifacts.

# Functional badge

## Generating Code per Backend
As stated in our paper section 6.1.2, our tool can target 6 different backends for 69 benchmarks. To reproduce the result for all benchmarks, simpliy run 
```
poetry shell python tenspiler/generated_code/<backend>/generate_<backend>_benchmarks.py ALL
```
which would write the result of final lifted code to `tenspiler/generated_code/<backend>/<benchmark-suite>/<synthesized-file>`.

Note this could take a while. To only test a single benchmark, run
```
poetry shell python tenspiler/generated_code/<backend>/generate_<backend>_benchmarks.py <benchmark-name>
```

See below for valid backend names and benchmark names:
### Backend names
- numpy
- mlx
- pytorch
- tensorflow
- gemmini
- gaudi

### Benchmark suites and names
#### blend
- **0** color_burn (no germmini support)
- **1** color_dodge (no germmini support)
- **2** darken_blend (no germmini support)
- **3** dissolve_blend (no germmini support)
- **4** lighten_blend (no germmini support)
- **5** linear_burn
- **6** linear_dodge
- **7** multiply_blend (no germmini support)
- **8** normal_blend
- **9** normal_blend_f
- **10** overlay_blend (no germmini support)
- **11** screen_blend

#### llama
- **0** matmul (no gaudi TPC-C support)
- **1** rmsnorm_part1 (no gaudi TPC-C support)
- **2** rmsnorm_part2 (no germmini support) (no gaudi TPC-C support)
- **3** softmax_part1 (no germmini support) (no gaudi TPC-C support)
- **4** softmax_part2 (no germmini support) (no gaudi TPC-C support)
- **5** softmax_part3 (no gaudi TPC-C support)
- **6** softmax_part4 (no germmini support) (no gaudi TPC-C support)
- **7** transformer_part1 (no germmini support) (no gaudi TPC-C support)
- **8** transformer_part2 (no germmini support) (no gaudi TPC-C support)
- **9** transformer_part3 (no germmini support) (no gaudi TPC-C support)
- **10** transformer_part4 (no germmini support) (no gaudi TPC-C support)

#### blas
- **0** dot
- **1** gemv (no gaudi TPC-C support)

#### darknet
- **0** mag_array
- **1** matrix_add_matrix
- **2** mse_array
- **3** mult_add_into_cpu
- **4** ol_l2_cpu1
- **5** ol_l2_cpu2
- **6** scale_array
- **7** scale_matrix
- **8** sum_array
- **9** translate_array (no germmini support)

#### utdsp
- **0** fir_small
- **1** lmsfir1
- **2** lmsfir2

#### dsp
- **0** matadd
- **1** matscal
- **2** matsub
- **3** vadd
- **4** vcopy (no germmini support) (no gaudi TPC-C support)
- **5** vmul (no germmini support)
- **6** vneg (no germmini support)
- **7** voffset (no germmini support)
- **8** vrecip (no germmini support)
- **9** vscal
- **10** vsub
- **11** wvec

#### dspstone
- **0** mat1x3 (no gaudi TPC-C support)
- **1** n_real_updates 

#### makespeare
- **0** sum_of_squares

#### mathfu
- **0** diveq (no germmini support)
- **1** diveq_sca
- **2** len
- **3** len_sq
- **4** matmul_sca
- **5** muleq (no germmini support)
- **6** muleq_sca
- **7** negate (no germmini support)
- **8** pluseq
- **9** subeq
- **10** subeq_sca (no germmini support)

#### simple_array
- **0** array_inc (no germmini support)
- **1** array_sum
- **2** cube_in_place (no germmini support)
- **3** fourth_in_place (no germmini support)
- **4** sum_elts


## Performance Evaluation
In Figure 9 and 10, we have shown the performance of lifted code compared to C++ baseline. In this artifact, we include scripts to regenerate the results. 

However, our evaluation in paper was done using either 10k images from ImageNet or the model weights from vicuna-33B and 7B. Evaluation of the full datasets could take a long time to run. Thus, we included the scaled down versions to use for artifact review. To retrieve the full datasets: 10k images can be downloaded at `https://drive.google.com/drive/folders/1sH1HwGeovQ2AA81WmL6H7fQFk0GvwhTj?usp=sharing`, vicuna weight 33B and 7B can be obtained by runing in `poetry shell python tenspiler/benchmarking/retrieving_data/vicuna_weights_processing.py`. 

Before running a test, decide the datasets to use and rename them appropriately so the timing scripts can locate them by running

```
cp -rfT ./data_sampled/ ./data/
cp -f ./vicuna_weight_sampled.h5 ./vicuna_weight.h5
cp -f ./vicuna_weight7b_sampled.h5 ./vicuna_weight7b.h5
```
replace _sampled with _full if using full dataset.

Also, evaluations of TensorFlow and PyTorch were using GPU which aren't supported by Docker ([comment]TODO: do we want to add support?) so the scripts will execute them on CPU. 

The MLX library requires Apple's M-series CPU. To run these, port all files onto a platform with M-series chip, install MLX with `pip install mlx==0.7`, and follow the same command.

Germmini requires setup Dockerfile currently not support. Please follow [comment]TODO: add how to setup germmini for evaluation?.

Gaudi requires specialized Gaudi2 hardware, available in AWS EC2 DL1 instance, for execution. [comment]TODO: add how to set this up?
[comment]: we can skip the C++ setup here
[comment]: im not sure how to run gaudi code yet. do we need to mention that?

We recognize some of the backends are hard to setup for execution, but we have verified the code with Germmini and Gaudi experts as well as running them. For fast verification in Docker, please use NumPy, TensorFlow, or PyTorch as backend.

To obtain runtime comparision of a backend with baseline over all benchmarks, run
```
poetry shell python tenspiler/benchmarking/<backend>_speedup_exec.py ALL
```
This runs all supported benchmarks twice: with C++ baseline and the specified backend, so it could take few hours.

For evaluation of one benchmark, run 
```
poetry shell python tenspiler/benchmarking/<backend>_speedup_exec.py <benchmark-name>
```
The execution results are printed to the terminal. 


## Synthesis Timing and Abolation Timing
[comment]TODO: do we include this?
The synthesize timing presented in Figure 8 can be reproduced by running [comment]TODO(jie): add how to get synthesize timing data. The abolation timing study in Figure 11 can be reproduced by running [comment]TODO(jie): add how to get data for abolation study

# Reusable badge

Our implementation is open-source, and it's also easy to add another backend as described in section 6.1.2. To add a backend, all we need is to write a code-generation script in `tenspiler/codegen/`. 

Taking MLX as an example, in the script `mlx_codegen.py`, we first define a dict with the mapping of TenIR operations to library specific function calls formatted as a lambda that takes in a list of arguments.
```python
translations = {
    VEC_ELEMWISE_ADD: lambda processed_args: f"({processed_args[0]}) + ({processed_args[1]})",
    MATRIX_ELEMWISE_ADD: lambda processed_args: f"({processed_args[0]}) + ({processed_args[1]})",
    ...
}
```
Then, we can reuse one of the existing `<backend>_codegen` function from another backend which will recursively parse the IR tree corresponding to our synthesized solution. This can be used to generate the body of the resulting function as string. To actual executable code, we add the import-statements needed as well as function definition to insert the body into. And optionally any glue-code that can connect other input format (e.g. Python List) to the desired solution. To generate code targeting this new backend, we call this `<backend>_codegen` with results from any synthesizing driver.

[comment] : we can add few things about driver. [comment]TODO(jie): could u add the drivers info