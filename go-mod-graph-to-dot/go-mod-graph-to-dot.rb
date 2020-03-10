#!/usr/bin/env ruby

def shorten_label(label)
  label = label.gsub(/\@.*$/, "")
  label = label.gsub(/github\.com/, "")
  label = label.gsub(/golang\.org/, "")
  label
end

nodes = {}
edges = []

next_node_id = 1

$stdin.read.each_line do |line|
  src, dst = line.split(" ")

  if nodes.include?(src)
    src_id = nodes[src]
  else
    src_id = next_node_id
    nodes[src] = src_id
    next_node_id += 1
  end

  if nodes.include?(dst)
    dst_id = nodes[dst]
  else
    dst_id = next_node_id
    nodes[dst] = dst_id
    next_node_id += 1
  end

  edges.push([src_id, dst_id])
end

puts "digraph go_mod_graph {"

puts "  graph [layout = dot, rankdir = LR];"

nodes.each do |label, node_id|
  puts "  n#{node_id} [label = \"#{shorten_label(label)}\"]";
end

edges.each do |src_id, dst_id|
  puts "  n#{src_id} -> n#{dst_id};"
end

puts "}"
