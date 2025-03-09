#!/usr/bin/env python3

# Import the verifier function from the geometric_verifier module
from geometric_verifier import verify_geometric_proof


def main():
    """
    Simple script to demonstrate using the geometric verifier.
    The paths to the proof files are hardcoded in this script.
    """
    # Define the paths to your proof files here
    proof_paths = [
        "/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_45_questions/question_464/question464_gt",
        # Add more paths here if needed
    ]

    all_passed = True

    for proof_path in proof_paths:
        print(f"\nVerifying proof at: {proof_path}")

        # Call the verification function with the provided path
        result, feedback = verify_geometric_proof(proof_path)

        # Print the result
        if result:
            print("✅ Verification SUCCEEDED")
        else:
            all_passed = False
            print("❌ Verification FAILED")
            print("Feedback:")
            print(feedback)

    if all_passed:
        print("\nAll proofs verified successfully!")
    else:
        print("\nSome proofs failed verification.")

    return all_passed


if __name__ == "__main__":
    main()