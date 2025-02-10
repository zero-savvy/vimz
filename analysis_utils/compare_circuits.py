import sys

import pandas as pd
from tabulate import tabulate

from analyze_circuits import parameters

if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise ValueError("Invalid number of arguments. Usage: python compare_circuits.py <param_file_1> <param_file_2>")
    params_1, params_2 = pd.read_csv(sys.argv[1]), pd.read_csv(sys.argv[2])

    comparison = pd.merge(params_1, params_2, on="File Name", suffixes=("_1", "_2"))

    for col in parameters:
        comparison[f"{col} Diff"] = comparison[f"{col}_1"] - comparison[f"{col}_2"]

    diff_columns = ["File Name"] + [f"{col} Diff" for col in parameters]
    diff_table = comparison[diff_columns]

    print(tabulate(diff_table, headers="keys", tablefmt="grid"))
