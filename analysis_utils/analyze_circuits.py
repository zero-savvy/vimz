import sys

import pandas as pd
from tabulate import tabulate

parameters = [
    "Template Instances", "Non-Linear Constraints", "Linear Constraints",
    "Public Inputs", "Private Inputs", "Public Outputs", "Wires", "Labels"
]


def parse_logs_to_dataframe(log_files):
    data = []
    for log_file in log_files:
        base_name = log_file.split("/")[-1].removesuffix("_step.compile_log")
        with open(log_file, 'r') as f:
            content = f.readlines()
            metrics = {"File Name": base_name} | {key: 0 for key in parameters}
            for line in content:
                for key in metrics.keys():
                    if key.lower() in line.lower():
                        metrics[key] = int(line.split(":")[1].strip().split(" ")[0])
            data.append(metrics)
    return pd.DataFrame(data)


def gather_circuit_parameters(backend):
    transformations = ["blur", "brightness", "contrast", "crop", "grayscale", "hash", "resize", "sharpness"]
    files = [f"circuits/{backend}/{t}_step.compile_log" for t in transformations]
    return parse_logs_to_dataframe(files)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError("Invalid number of arguments. Usage: python analyze_circuits.py <backend>")
    backend = sys.argv[1]

    if backend not in ["nova_snark", "sonobe"]:
        raise ValueError("Invalid backend. Must be either 'nova_snark' or 'sonobe'.")

    print(tabulate(gather_circuit_parameters(backend), headers="keys", tablefmt="grid"))
