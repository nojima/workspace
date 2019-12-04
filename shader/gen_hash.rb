def vec(dim)
  if dim == 1
    return "float"
  else
    return "vec#{dim}"
  end
end

def uvec(dim)
  if dim == 1
    return "uint"
  else
    return "uvec#{dim}"
  end
end

def murmur_hash_code(in_dim, out_dim)
  seeds = [1190494759, 2147483647, 3559788179, 179424673]
  seed_vec = seeds.take(out_dim).map{|seed| "#{seed}u"}.join(", ")
  seed_vec = "#{uvec(out_dim)}(#{seed_vec})" if out_dim > 1

  code1 = <<~EOS
  #{uvec(out_dim)} murmurHash#{out_dim}#{in_dim}(#{uvec(in_dim)} src) {
      const uint M = 0x5bd1e995u;
      #{uvec(out_dim)} h = #{seed_vec};
      src *= M; src ^= src>>24u; src *= M;
  EOS

  code2 = "    " + if in_dim == 1
    "h *= M; h ^= src;"
  else
    %w(x y z w).take(in_dim).map{|x| "h *= M; h ^= src.#{x};"}.join(" ")
  end

  code3 = <<~EOS
      h ^= h>>13u; h *= M; h ^= h>>15u;
      return h;
  }
  EOS

  return [code1.chomp, code2, code3].join("\n")
end

def hash_code(in_dim, out_dim)
  return <<~EOS
  #{vec(out_dim)} hash#{out_dim}#{in_dim}(#{vec(in_dim)} src) {
      #{uvec(out_dim)} h = murmurHash#{out_dim}#{in_dim}(floatBitsToUint(src));
      return uintBitsToFloat(h & 0x007fffffu | 0x3f800000u) - 1.0;
  }
  EOS
end

def main
  puts "// Hash Functions"
  puts "//"
  puts "// murmurHashNM() takes M unsigned integers and returns N hash values."
  puts "// The returned values are unsigned integers between 0 and 2^32 - 1."
  puts "//"
  puts "// hashNM() takes M floating point numbers and returns N hash values."
  puts "// The returned values are floating point numbers between 0.0 and 1.0."
  puts
  (1..4).each do |out_dim|
    (1..4).each do |in_dim|
      puts "//------------------------------------------------------------------------------"
      puts
      puts murmur_hash_code(in_dim, out_dim)
      puts
      puts "// #{out_dim} output#{out_dim > 1 ? "s" : ""}, #{in_dim} input#{in_dim > 1 ? "s" : ""}"
      puts hash_code(in_dim, out_dim)
      puts
    end
  end
end

main
