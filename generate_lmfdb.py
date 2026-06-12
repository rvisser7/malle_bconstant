import glob

def get_sort_key(group_label):
    # Splits "30T132" into (30, 132) to ensure 6T1 comes before 30T1
    parts = group_label.split('T')
    return (int(parts[0]), int(parts[1]))

def generate_lmfdb_files(input_pattern="BW_Bounds_Degree_*.txt", 
                         lmfdb_file="lmfdb_malle_b.txt", 
                         unknown_file="unknown_wang_b.txt"):
                         
    file_list = glob.glob(input_pattern)
    
    if not file_list:
        print(f"No files found matching the pattern: {input_pattern}")
        return
        
    parsed_data = []
    unknown_labels = []
    
    # ---------------------------------------------------------
    # 1. Parse the Magma output files
    # ---------------------------------------------------------
    for filepath in file_list:
        with open(filepath, 'r') as infile:
            for line in infile:
                line = line.strip()
                
                if line.startswith("Group "):
                    # Example line: 
                    # "Group 30T132: b_M = 1, b_T = 1, BW_lower_split = 1, BW_upper_local = 1"
                    try:
                        label_part, vars_part = line.split(":")
                        label = label_part.replace("Group ", "").strip()
                        
                        var_dict = {}
                        for kv in vars_part.split(","):
                            k, v = kv.split("=")
                            var_dict[k.strip()] = int(v.strip())
                            
                        b_M = var_dict['b_M']
                        b_T = var_dict['b_T']
                        bw_l = var_dict['BW_lower_split']
                        bw_u = var_dict['BW_upper_local']
                        
                        parsed_data.append((label, b_M, b_T, bw_l, bw_u))
                    except Exception as e:
                        print(f"Could not parse line: {line} \nError: {e}")

    # Sort mathematically by degree, then by T-number
    parsed_data.sort(key=lambda x: get_sort_key(x[0]))
    
    # ---------------------------------------------------------
    # 2. Database format setup
    # ---------------------------------------------------------
    # NOTE: LMFDB uses PostgreSQL. If you are doing a raw bulk import (.txt copy),
    # Postgres usually requires "\N" to represent a NULL smallint. 
    # I have set this to "None" as requested, but you can change it here if the DB rejects it!
    NULL_STRING = "None" 
    
    with open(lmfdb_file, 'w') as f_lmfdb, open(unknown_file, 'w') as f_unk:
        
        # Write LMFDB headers
        f_lmfdb.write("label|malle_turkelli_b|malle_wang_b|malle_b_status\n")
        f_lmfdb.write("text|smallint|smallint|smallint\n\n")
        
        for label, b_M, b_T, bw_l, bw_u in parsed_data:
            
            # --- Determine Wang's b-constant ---
            if bw_l == bw_u:
                b_W_str = str(bw_l)
            else:
                b_W_str = NULL_STRING
                unknown_labels.append(label)
                
            # --- Determine the status (0, 1, 2, or 3) ---
            # We check all mathematically possible values for b_W in the range [bw_l, bw_u]
            possible_statuses = set()
            for x in range(bw_l, bw_u + 1):
                if b_M == x and x == b_T:
                    possible_statuses.add(0)    # b_M = b_W = b_T
                elif b_M < x and x == b_T:
                    possible_statuses.add(1)    # b_M < b_W = b_T
                elif b_M == x and x < b_T:
                    possible_statuses.add(2)    # b_M = b_W < b_T
                elif b_M < x and x < b_T:
                    possible_statuses.add(3)    # b_M < b_W < b_T
                    
            # If all possible values of b_W yield the exact same relational status, we deduced it!
            if len(possible_statuses) == 1:
                status_str = str(possible_statuses.pop())
            else:
                # The bounds are too wide; we cannot definitively deduce the status
                status_str = NULL_STRING
                
            # Write formatted row to the LMFDB file
            f_lmfdb.write(f"{label}|{b_T}|{b_W_str}|{status_str}\n")
            
        # Write the list of unknowns to the secondary file
        for label in unknown_labels:
            f_unk.write(f"{label}\n")

    # ---------------------------------------------------------
    # 3. Print Summary
    # ---------------------------------------------------------
    print("==========================================================")
    print(f"Processed {len(parsed_data)} group outputs.")
    print(f"Found {len(unknown_labels)} groups with an unknown Wang b-constant.")
    print("----------------------------------------------------------")
    print(f"LMFDB formatted data saved to: '{lmfdb_file}'")
    print(f"Unknown labels saved to:       '{unknown_file}'")
    print("==========================================================")

if __name__ == "__main__":
    # Ensure this pattern matches the Magma output files in your directory!
    generate_lmfdb_files(input_pattern="BW_Bounds_Degree_*.txt")
