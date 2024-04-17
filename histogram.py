import matplotlib.pyplot as plt
import argparse

def opcode_histogram(filename):
  """
  This function reads a file with lines with "EVM OpCode time_in_nanoseconds" and generates a histogram showing total time per opcode.

  Args:
    filename: The path to the input file.
  """
  opcodes_time = {}
  opcodes_count = {}
  opcodes_mean = {}
  with open(filename, 'r') as f:
    for line in f:
      try: 
        opcode, time_str = line.strip().split()
      except ValueError:
        print(f"Error in {line}")
        return
      time_in_ns = int(time_str)
      opcodes_time[opcode] = opcodes_time.get(opcode, 0) + time_in_ns
      opcodes_count[opcode] = opcodes_count.get(opcode, 0) + 1
      
      assert opcodes_time[opcode] >= time_in_ns, f"Overflow for {opcode} at {time_in_ns}"
      assert opcodes_count[opcode] >= 1, f"Overflow for {opcode} at {time_in_ns}"
  
  # Calculate the mean time spent in each opcode
  for opcode in opcodes_time:
    opcodes_mean[opcode] = opcodes_time[opcode] / opcodes_count[opcode]
  
  # Sort by keys
  opcodes_time = dict(sorted(opcodes_time.items(), key=lambda x: int(x[0])))
  opcodes_count = dict(sorted(opcodes_count.items(), key=lambda x: int(x[0])))
  opcodes_mean = dict(sorted(opcodes_mean.items(), key=lambda x: int(x[0])))
  
  # Save the agregatted data as "keys count total_time mean_time"
  with open("aggregated_data.txt", 'w') as f:
    for key in opcodes_time:
      f.write(f"{key} {opcodes_count[key]} {opcodes_time[key]} {opcodes_mean[key]}\n")

  # Extract opcodes and total times into separate lists
  opcodes_list = list(opcodes_time.keys())
  times_list = list(opcodes_time.values())
  count_list = list(opcodes_count.values())
  mean_list = list(opcodes_mean.values())
  
  # Print the number of different OpCodes
  print("Number of different opcodes: ", len(opcodes_list))
  
  # Generate the histogram and save it to a file named "total_time_histogram.png"
  plt.figure(figsize=(45, 15))
  plt.bar(opcodes_list, times_list)
  plt.xlabel("Opcode")
  plt.ylabel("Total Time (ns)")
  plt.title("Histogram of Total Time Spent in Each Opcode")
  plt.xticks(rotation=45, ha='right', fontsize=13)
  plt.tight_layout()
  plt.savefig("total_time_histogram.png")
  
  # Generate the histogram and save it to a file named "count_histogram.png"
  plt.figure(figsize=(60, 15))
  plt.bar(opcodes_list, count_list)
  plt.xlabel("Opcode")
  plt.ylabel("Count")
  plt.title("Histogram of How Many Times Each Opcode was Executed")
  plt.xticks(rotation=60, ha='right', fontsize=13)
  plt.tight_layout()
  plt.savefig("count_histogram.png")
  
  
  # Generate the histogram and save it to a file named "mean_histogram.png"
  plt.figure(figsize=(60, 15))
  plt.bar(opcodes_list, mean_list)
  plt.xlabel("Opcode")
  plt.ylabel("Mean Time (ns)")
  plt.title("Histogram of Mean Time Spent in Each Opcode")
  plt.xticks(rotation=45, ha='right', fontsize=13)
  plt.tight_layout(pad=0.05)
  plt.savefig("mean_histogram.png")
  
  

# Usage: `python3 histogram.py kevm-pyk/hook_times.txt`
if __name__ == "__main__":
  parser = argparse.ArgumentParser(description='Generate histograms from an input file.')
  parser.add_argument('filename', type=str, help='The path to the input file.')
  args = parser.parse_args()
  filename = args.filename

opcode_histogram(filename)

