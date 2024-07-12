import matplotlib.pyplot as plt

# Sample data
x_labels = ["Depth 1", "Depth 2", "Depth 3", "Depth 4", "Depth 5"]
values = [6.107, 11.917, 23.815, 38.142, 184.59]

# Create bar chart
plt.bar(x_labels, values, color="skyblue")

# Adding labels and title
plt.ylabel("Synthesis Time (Seconds)")
# plt.title('Bar Chart Example')

# Display the plot
plt.savefig(f"3d-synth-timing.png", format="png", dpi=600)
