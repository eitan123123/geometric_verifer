import os
import sys
import io
import contextlib
import re
from geometric_verifier import verify_geometric_proof


def verify_all_proofs(base_directory):
    # List of question numbers to specifically check
    required_questions = [
        51, 69, 127, 178, 192, 246, 358, 437, 449, 464, 532, 696, 716, 844, 847,
        1258, 1490, 1726, 1854, 1945, 1975, 2106, 2114, 2196, 2200, 2323, 2410, 2425, 2614, 4099,
        2624, 2669, 2761, 2851, 2875, 2916, 2999, 3027, 3272, 3412,  3418 , 3983, 4187, 4254, 4473, 4476,
        4483, 4523, 4796, 4797, 4892, 4898, 4910, 4923, 5230, 5208, 5399, 5431, 5510, 5645, 5708, 5779, 5805,
        5808, 6018, 6417, 6155, 6247, 6485 , 6790, 6802, 6924
    ]
    results = []

    # First collect all directories and their results
    for entry in os.listdir(base_directory):
        entry_path = os.path.join(base_directory, entry)

        # Check if the entry is a directory and starts with 'question'
        if os.path.isdir(entry_path) and entry.startswith('question'):
            question_number = entry.replace('question', '')

            # Try different possible file naming patterns
            possible_paths = [
                os.path.join(entry_path, f"question{question_number}_gt"),  # Original pattern
                os.path.join(entry_path, "question_gt"),  # Generic name
                os.path.join(entry_path, "gt"),  # Just "gt"
            ]

            # Find files that might contain "gt" in the name
            gt_files = [f for f in os.listdir(entry_path) if "gt" in f.lower()]
            if gt_files:
                # Add any found files to our possible paths
                for gt_file in gt_files:
                    possible_paths.append(os.path.join(entry_path, gt_file))

            # Try each possible path
            gt_path = None
            for path in possible_paths:
                if os.path.exists(path):
                    gt_path = path
                    break

            # Extract question number as an integer for sorting
            question_num = int(re.search(r'\d+', question_number).group())

            # Check if we found a valid file
            if gt_path and os.path.isfile(gt_path):
                try:
                    # Capture all output from verify_geometric_proof
                    with contextlib.redirect_stdout(io.StringIO()):
                        with contextlib.redirect_stderr(io.StringIO()):
                            result, feedback = verify_geometric_proof(gt_path)  # Unpack the tuple
                            results.append((question_num, entry, 'SUCCEEDED' if result else 'FAILED'))
                except Exception as e:
                    results.append((question_num, entry, f'ERROR - {type(e).__name__}'))
            else:
                results.append((question_num, entry, 'ERROR - File not found'))

    # Sort the results by question number
    results.sort()

    # Print the sorted results
    for question_num, entry, status in results:
        print(f"{entry}: {status}")

    # Check if all required questions succeeded
    required_results = {q: 'NOT FOUND' for q in required_questions}
    for question_num, entry, status in results:
        if question_num in required_questions:
            required_results[question_num] = status

    # Check if all required questions succeeded
    all_succeeded = all(status == 'SUCCEEDED' for status in required_results.values())
    print("\n" + "=" * 50)
    if all_succeeded:
        print("All required questions succeeded!")
    else:
        print("Not all required questions succeeded. Failed questions:")
        for q_num, status in sorted(required_results.items()):
            if status != 'SUCCEEDED':
                print(f"Question {q_num}: {status}")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        base_dir = sys.argv[1]
    else:
        base_dir = "/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_45_questions"
    verify_all_proofs(base_dir)