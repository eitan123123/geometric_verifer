import os
import sys
import io
import contextlib
import re
from geometric_verifier import verify_geometric_proof


def verify_all_proofs(base_directory):
    results = []

    # First collect all directories and their results
    for entry in os.listdir(base_directory):
        entry_path = os.path.join(base_directory, entry)

        # Check if the entry is a directory and starts with 'question_'
        if os.path.isdir(entry_path) and entry.startswith('question_'):
            question_number = entry.replace('question_', '')
            gt_filename = f"question{question_number}_gt"
            gt_path = os.path.join(entry_path, gt_filename)

            # Extract question number as an integer for sorting
            question_num = int(re.search(r'\d+', question_number).group())

            # Check if the expected file exists
            if os.path.isfile(gt_path):
                try:
                    # Capture all output from verify_geometric_proof
                    with contextlib.redirect_stdout(io.StringIO()):
                        with contextlib.redirect_stderr(io.StringIO()):
                            result = verify_geometric_proof(gt_path)

                    results.append((question_num, entry, 'SUCCEEDED' if result else 'FAILED'))
                except Exception as e:
                    results.append((question_num, entry, f'ERROR - {type(e).__name__}'))
            else:
                results.append((question_num, entry, 'ERROR - File not found'))

    # Sort the results by question number
    results.sort()

    # Print the sorted results
    for _, entry, status in results:
        print(f"{entry}: {status}")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        base_dir = sys.argv[1]
    else:
        base_dir = "/Users/eitanstern/Desktop/orens_code/geometric_verifer/questions/the new format for questions after jan_17/new_45_questions"

    verify_all_proofs(base_dir)