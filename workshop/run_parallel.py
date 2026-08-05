import subprocess
import multiprocessing
from concurrent.futures import ProcessPoolExecutor

def run_magma_for_degree(n):
    """Spawns a Magma process for a specific degree n."""
    print(f"[{n}] Thread started...")
    
    # The command line arguments to run Magma.
    # The "-b" flag runs Magma in batch mode (no user prompts).
    # "n:={n}" passes the degree parameter into the Magma environment.
    cmd = ["magma", "-b", f"n:={n}", "unified_script.m"]
    
    try:
        # Execute the Magma script. 
        # Output is routed to DEVNULL so it doesn't flood your Python console,
        # since the Magma script already logs everything safely to text files!
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT, check=True)
        print(f"[{n}] Thread finished successfully! Output saved to file.")
    except subprocess.CalledProcessError as e:
        print(f"[{n}] ERROR: Magma process crashed.")

if __name__ == "__main__":
    # ---------------------------------------------------------
    # Configuration
    # ---------------------------------------------------------
    # Create a list of the degrees you want to compute
    degrees_to_evaluate = list(range(2, 13))  # Computes degrees 2 through 12
    
    # Determine how many threads to run simultaneously.
    # By default, this uses all available CPU cores minus 1 (to leave your OS responsive).
    total_cores = multiprocessing.cpu_count()
    max_parallel_jobs = max(1, total_cores - 1) 
    
    print(f"Starting parallel execution using {max_parallel_jobs} cores...")
    print("==========================================================")
    
    # ---------------------------------------------------------
    # Execution
    # ---------------------------------------------------------
    with ProcessPoolExecutor(max_workers=max_parallel_jobs) as executor:
        # Map the list of degrees to our Magma runner function
        executor.map(run_magma_for_degree, degrees_to_evaluate)
        
    print("==========================================================")
    print("All parallel jobs completed!")
