/*
    This file is part of TON Blockchain Library.

    TON Blockchain Library is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    TON Blockchain Library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with TON Blockchain Library.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2017-2020 Telegram Systems LLP
*/

#include <vector>

#include <functional>
#include "vm/tonops.h"
#include "vm/log.h"
#include "vm/opctable.h"
#include "vm/stack.hpp"
#include "vm/excno.hpp"
#include "vm/vm.h"
#include "vm/dict.h"
#include "vm/boc.h"
#include "Ed25519.h"

#include "openssl/digest.hpp"

#include <nil/crypto3/algebra/curves/mnt4.hpp>
#include <nil/crypto3/algebra/fields/mnt4/base_field.hpp>
#include <nil/crypto3/algebra/fields/mnt4/scalar_field.hpp>
#include <nil/crypto3/algebra/fields/arithmetic_params/mnt4.hpp>
#include <nil/crypto3/algebra/curves/params/multiexp/mnt4.hpp>
#include <nil/crypto3/algebra/curves/params/wnaf/mnt4.hpp>

#include <nil/crypto3/zk/snark/sparse_vector.hpp>
#include <nil/crypto3/zk/snark/accumulation_vector.hpp>

#include <nil/crypto3/zk/snark/proof_systems/ppzksnark/r1cs_gg_ppzksnark.hpp>

#include <nil/crypto3/multiprecision/number.hpp>
#include <nil/crypto3/multiprecision/cpp_int.hpp>
#include <nil/crypto3/multiprecision/modular/modular_adaptor.hpp>

#include <nil/crypto3/detail/pack.hpp>
#include <nil/crypto3/detail/stream_endian.hpp>

namespace vm {
namespace detail {

using namespace nil::crypto3::zk::snark;

template <typename ProofSystem>
struct verifier_data_from_bits;

template <typename CurveType>
struct verifier_data_from_bits<r1cs_gg_ppzksnark<CurveType>> {
  using proof_system = r1cs_gg_ppzksnark<CurveType>;

  typedef typename CurveType::base_field_type::modulus_type modulus_type;
  typedef typename CurveType::base_field_type::number_type number_type;

  constexpr static const std::size_t modulus_bits = CurveType::base_field_type::modulus_bits;

  typedef std::uint8_t chunk_type;

  constexpr static const std::size_t chunk_size = 8;
  constexpr static const std::size_t modulus_chunks = modulus_bits / chunk_size + modulus_bits % chunk_size;

  template <typename FieldType>
  static inline typename std::enable_if<!::nil::crypto3::detail::is_extended_field<FieldType>::value,
                                        typename FieldType::value_type>::type
  field_type_process(typename std::vector<chunk_type>::const_iterator& read_iter) {
    using field_type = FieldType;

    modulus_type fp_out;

    nil::crypto3::multiprecision::import_bits(fp_out, read_iter, read_iter + modulus_chunks, chunk_size, false);

    read_iter += modulus_chunks;

    return typename field_type::value_type(fp_out);
  }

  template <typename FieldType>
  static inline typename std::enable_if<::nil::crypto3::detail::is_extended_field<FieldType>::value,
                                        typename FieldType::value_type>::type
  field_type_process(typename std::vector<chunk_type>::const_iterator& read_iter) {
    using field_type = FieldType;

    typename field_type::value_type::data_type data;
    const std::size_t data_dimension = field_type::arity / field_type::underlying_field_type::arity;

    for (int n = 0; n < data_dimension; ++n) {
      data[n] = field_type_process<typename field_type::underlying_field_type>(read_iter);
    }

    return typename field_type::value_type(data);
  }

  template <typename GroupType>
  static inline typename GroupType::value_type group_type_process(
      typename std::vector<chunk_type>::const_iterator& read_iter) {
    typename GroupType::underlying_field_type::value_type X =
        field_type_process<typename GroupType::underlying_field_type>(read_iter);

    typename GroupType::underlying_field_type::value_type Y =
        field_type_process<typename GroupType::underlying_field_type>(read_iter);

    typename GroupType::underlying_field_type::value_type Z =
        field_type_process<typename GroupType::underlying_field_type>(read_iter);

    return typename GroupType::value_type(X, Y, Z);
  }

  static inline std::size_t std_size_t_process(typename std::vector<chunk_type>::const_iterator& read_iter) {
    std::vector<std::size_t> vector_s(1, 0);
    auto iter = vector_s.begin();

    std::size_t vector_c_size = 4;
    std::vector<chunk_type> vector_c;

    vector_c.reserve(vector_c_size);
    vector_c.insert(vector_c.end(), read_iter, read_iter + vector_c_size);

    nil::crypto3::detail::pack_from<nil::crypto3::stream_endian::big_octet_big_bit, 8, 32>(vector_c, iter);

    read_iter += sizeof(std::size_t);

    return vector_s[0];
  }

  template <typename T>
  static inline sparse_vector<T> sparse_vector_process(typename std::vector<chunk_type>::const_iterator& read_iter) {
    std::size_t indices_count = std_size_t_process(read_iter);

    std::vector<std::size_t> indices(indices_count, 0);

    for (std::size_t i = 0; i < indices_count; i++) {
      indices[i] = std_size_t_process(read_iter);
    }

    std::size_t values_count = std_size_t_process(read_iter);

    std::vector<typename T::value_type> values(values_count);

    for (std::size_t i = 0; i < values_count; i++) {
      values[i] = group_type_process<T>(read_iter);
    }

    std::size_t domain_size_ = std_size_t_process(read_iter);

    sparse_vector<T> sv;

    sv.indices = indices;
    sv.values = values;
    sv.domain_size_ = domain_size_;

    return sv;
  }

  template <typename T>
  static inline accumulation_vector<T> accumulation_vector_process(
      typename std::vector<chunk_type>::const_iterator& read_iter) {
    typename T::value_type first = group_type_process<T>(read_iter);
    sparse_vector<T> rest = sparse_vector_process<T>(read_iter);

    return accumulation_vector<T>(std::move(first), std::move(rest));
  }

  static inline typename proof_system::verification_key_type verification_key_process(
      typename std::vector<chunk_type>::const_iterator& read_iter) {
    using verification_key_type = typename proof_system::verification_key_type;

    typename CurveType::gt_type::value_type alpha_g1_beta_g2 =
        field_type_process<typename CurveType::gt_type>(read_iter);
    typename CurveType::g2_type::value_type gamma_g2 = group_type_process<typename CurveType::g2_type>(read_iter);
    typename CurveType::g2_type::value_type delta_g2 = group_type_process<typename CurveType::g2_type>(read_iter);

    accumulation_vector<typename CurveType::g1_type> gamma_ABC_g1 =
        accumulation_vector_process<typename CurveType::g1_type>(read_iter);

    // verification_key_type vk = verification_key_type (
    //    alpha_g1_beta_g2, gamma_g2, delta_g2, gamma_ABC_g1);

    return verification_key_type(alpha_g1_beta_g2, gamma_g2, delta_g2, gamma_ABC_g1);
  }

  static inline typename proof_system::primary_input_type primary_input_process(
      typename std::vector<chunk_type>::const_iterator& read_iter) {
    using primary_input_type = typename proof_system::primary_input_type;

    std::size_t pi_count = std_size_t_process(read_iter);

    std::vector<typename CurveType::scalar_field_type::value_type> pi(pi_count);

    for (std::size_t i = 0; i < pi_count; i++) {
      pi[i] = field_type_process<typename CurveType::scalar_field_type>(read_iter);
    }

    return primary_input_type(pi);
  }

  static inline typename proof_system::proof_type proof_process(
      typename std::vector<chunk_type>::const_iterator& read_iter) {
    using proof_type = typename proof_system::proof_type;

    typename CurveType::g1_type::value_type g_A = group_type_process<typename CurveType::g1_type>(read_iter);
    typename CurveType::g2_type::value_type g_B = group_type_process<typename CurveType::g2_type>(read_iter);
    typename CurveType::g1_type::value_type g_C = group_type_process<typename CurveType::g1_type>(read_iter);

    proof_type pr = proof_type(std::move(g_A), std::move(g_B), std::move(g_C));
    return pr;
  }

 public:
  struct verifier_data {
    typename proof_system::verification_key_type vk;
    typename proof_system::primary_input_type pi;
    typename proof_system::proof_type pr;
  };

  template <typename DataType>
  static inline verifier_data process(const DataType& data) {
    return verifier_data();
  }

  static inline verifier_data process(const std::vector<chunk_type>& data) {
    typename std::vector<chunk_type>::const_iterator read_iter = data.begin();

    typename proof_system::verification_key_type vk = verification_key_process(read_iter);

    typename proof_system::primary_input_type pi = primary_input_process(read_iter);

    typename proof_system::proof_type pr = proof_process(read_iter);

    return {vk, pi, pr};
  }
};

template <typename ProofSystem>
class verifier_data_to_bits;

// TODO: reimplement private functions using field value type trait
template <typename CurveType>
class verifier_data_to_bits<r1cs_gg_ppzksnark<CurveType>> {
  using proof_system = r1cs_gg_ppzksnark<CurveType>;

  constexpr static const std::size_t modulus_bits = CurveType::base_field_type::modulus_bits;

  typedef nil::crypto3::multiprecision::number<nil::crypto3::multiprecision::backends::cpp_int_backend<>> modulus_type;

  typedef std::uint8_t chunk_type;

  constexpr static const std::size_t chunk_size = 8;
  constexpr static const std::size_t modulus_chunks = modulus_bits / chunk_size + modulus_bits % chunk_size;

  template <typename FieldType>
  static inline typename std::enable_if<!::nil::crypto3::detail::is_extended_field<FieldType>::value, void>::type
  field_type_process(typename FieldType::value_type input_fp, typename std::vector<chunk_type>::iterator& write_iter) {
    nil::crypto3::multiprecision::export_bits(modulus_type(input_fp.data), write_iter, chunk_size, false);
    write_iter += modulus_chunks;
  }

  template <typename FieldType>
  static inline typename std::enable_if<::nil::crypto3::detail::is_extended_field<FieldType>::value, void>::type
  field_type_process(typename FieldType::value_type input_fp, typename std::vector<chunk_type>::iterator& write_iter) {
    using field_type = FieldType;

    const std::size_t data_dimension = field_type::arity / field_type::underlying_field_type::arity;

    for (int n = 0; n < data_dimension; ++n) {
      field_type_process<typename field_type::underlying_field_type>(input_fp.data[n], write_iter);
    }
  }

  template <typename GroupType>
  static inline void group_type_process(typename GroupType::value_type input_g,
                                        typename std::vector<chunk_type>::iterator& write_iter) {
    field_type_process<typename GroupType::underlying_field_type>(input_g.X, write_iter);
    field_type_process<typename GroupType::underlying_field_type>(input_g.Y, write_iter);
    field_type_process<typename GroupType::underlying_field_type>(input_g.Z, write_iter);
  }

  static inline void std_size_t_process(std::size_t input_s, std::vector<chunk_type>::iterator& write_iter) {
    std::vector<std::size_t> vector_s = {input_s};

    auto internal_write_iter = write_iter;
    nil::crypto3::detail::pack_to<nil::crypto3::stream_endian::big_octet_big_bit, 32, 8>(vector_s, internal_write_iter);

    write_iter += sizeof(std::size_t);
  }

  template <typename T>
  static inline void sparse_vector_process(sparse_vector<T> input_sp,
                                           typename std::vector<chunk_type>::iterator& write_iter) {
    std::size_t indices_count = input_sp.size();

    std_size_t_process(indices_count, write_iter);

    for (std::size_t i = 0; i < indices_count; i++) {
      std_size_t_process(input_sp.indices[i], write_iter);
    }

    std::size_t values_count = input_sp.values.size();

    std_size_t_process(values_count, write_iter);

    for (std::size_t i = 0; i < values_count; i++) {
      group_type_process<T>(input_sp.values[i], write_iter);
    }

    std_size_t_process(input_sp.domain_size_, write_iter);
  }

  template <typename T>
  static inline void accumulation_vector_process(accumulation_vector<T> input_acc,
                                                 typename std::vector<chunk_type>::iterator& write_iter) {
    group_type_process<T>(input_acc.first, write_iter);
    sparse_vector_process(input_acc.rest, write_iter);
  }

  static inline void verification_key_process(typename proof_system::verification_key_type vk,
                                              typename std::vector<chunk_type>::iterator& write_iter) {
    field_type_process<typename CurveType::gt_type>(vk.alpha_g1_beta_g2, write_iter);
    group_type_process<typename CurveType::g2_type>(vk.gamma_g2, write_iter);
    group_type_process<typename CurveType::g2_type>(vk.delta_g2, write_iter);

    accumulation_vector_process(vk.gamma_ABC_g1, write_iter);
  }

  static inline void primary_input_process(typename proof_system::primary_input_type pi,
                                           typename std::vector<chunk_type>::iterator& write_iter) {
    std::size_t pi_count = pi.size();

    std_size_t_process(pi_count, write_iter);

    for (std::size_t i = 0; i < pi_count; i++) {
      field_type_process<typename CurveType::scalar_field_type>(pi[i], write_iter);
    }
  }

  static inline void proof_process(typename proof_system::proof_type pr,
                                   typename std::vector<chunk_type>::iterator& write_iter) {
    group_type_process<typename CurveType::g1_type>(pr.g_A, write_iter);
    group_type_process<typename CurveType::g2_type>(pr.g_B, write_iter);
    group_type_process<typename CurveType::g1_type>(pr.g_C, write_iter);
  }

 public:
  struct verifier_data {
    typename proof_system::verification_key_type vk;
    typename proof_system::primary_input_type pi;
    typename proof_system::proof_type pr;
  };

  static inline std::vector<chunk_type> process(const verifier_data& vd) {
    std::size_t g1_size = modulus_chunks * 3 * CurveType::g1_type::underlying_field_type::arity; //48 * 3 * 1 = 144
    std::size_t g2_size = modulus_chunks * 3 * CurveType::g2_type::underlying_field_type::arity; //48 * 3 * 2 = 288
    std::size_t std_size_t_size = 4;

    std::size_t gt_size = modulus_chunks * CurveType::gt_type::underlying_field_type::arity; //48 * 12 = 576
    std::size_t sparse_vector_size = std_size_t_size + vd.vk.gamma_ABC_g1.rest.size() * std_size_t_size +
                                     std_size_t_size + vd.vk.gamma_ABC_g1.rest.values.size() * g1_size +
                                     std_size_t_size;

    std::size_t verification_key_size = gt_size + g2_size + g2_size + g1_size + sparse_vector_size;
    std::size_t primary_input_size = std_size_t_size + vd.pi.size() * modulus_chunks;
    std::size_t proof_size = g1_size + g2_size + g1_size;

    std::vector<chunk_type> output(2 * (verification_key_size + primary_input_size + proof_size));

    typename std::vector<chunk_type>::iterator write_iter = output.begin();

    verification_key_process(vd.vk, write_iter);

    primary_input_process(vd.pi, write_iter);

    proof_process(vd.pr, write_iter);

    return output;
  }

  static inline std::vector<chunk_type> process(typename proof_system::verification_key_type vk,
                                                typename proof_system::primary_input_type pi,
                                                typename proof_system::proof_type pr) {
    return process({vk, pi, pr});
  }

  static inline std::vector<chunk_type> process() {
    return process({});
  }
};

}  // namespace detail

namespace {

bool debug(const char* str) TD_UNUSED;
bool debug(const char* str) {
  std::cerr << str;
  return true;
}

bool debug(int x) TD_UNUSED;
bool debug(int x) {
  if (x < 100) {
    std::cerr << '[' << (char)(64 + x) << ']';
  } else {
    std::cerr << '[' << (char)(64 + x / 100) << x % 100 << ']';
  }
  return true;
}
}  // namespace

#define DBG_START int dbg = 0;
#define DBG debug(++dbg)&&
#define DEB_START DBG_START
#define DEB DBG

int exec_set_gas_generic(VmState* st, long long new_gas_limit) {
  if (new_gas_limit < st->gas_consumed()) {
    throw VmNoGas{};
  }
  st->change_gas_limit(new_gas_limit);
  return 0;
}

int exec_accept(VmState* st) {
  VM_LOG(st) << "execute ACCEPT";
  return exec_set_gas_generic(st, GasLimits::infty);
}

int exec_set_gas_limit(VmState* st) {
  VM_LOG(st) << "execute SETGASLIMIT";
  td::RefInt256 x = st->get_stack().pop_int_finite();
  long long gas = 0;
  if (x->sgn() > 0) {
    gas = x->unsigned_fits_bits(63) ? x->to_long() : GasLimits::infty;
  }
  return exec_set_gas_generic(st, gas);
}

int exec_commit(VmState* st) {
  VM_LOG(st) << "execute COMMIT";
  st->force_commit();
  return 0;
}

void register_basic_gas_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mksimple(0xf800, 16, "ACCEPT", exec_accept))
      .insert(OpcodeInstr::mksimple(0xf801, 16, "SETGASLIMIT", exec_set_gas_limit))
      .insert(OpcodeInstr::mksimple(0xf80f, 16, "COMMIT", exec_commit));
}

void register_ton_gas_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
}

int exec_get_param(VmState* st, unsigned idx, const char* name) {
  if (name) {
    VM_LOG(st) << "execute " << name;
  }
  Stack& stack = st->get_stack();
  auto tuple = st->get_c7();
  auto t1 = tuple_index(*tuple, 0).as_tuple_range(255);
  if (t1.is_null()) {
    throw VmError{Excno::type_chk, "intermediate value is not a tuple"};
  }
  stack.push(tuple_index(*t1, idx));
  return 0;
}

int exec_get_var_param(VmState* st, unsigned idx) {
  idx &= 15;
  VM_LOG(st) << "execute GETPARAM " << idx;
  return exec_get_param(st, idx, nullptr);
}

int exec_get_config_dict(VmState* st) {
  exec_get_param(st, 9, "CONFIGDICT");
  st->get_stack().push_smallint(32);
  return 0;
}

int exec_get_config_param(VmState* st, bool opt) {
  VM_LOG(st) << "execute CONFIG" << (opt ? "OPTPARAM" : "PARAM");
  Stack& stack = st->get_stack();
  auto idx = stack.pop_int();
  exec_get_param(st, 9, nullptr);
  Dictionary dict{stack.pop_maybe_cell(), 32};
  td::BitArray<32> key;
  Ref<vm::Cell> value;
  if (idx->export_bits(key.bits(), key.size(), true)) {
    value = dict.lookup_ref(key);
  }
  if (opt) {
    stack.push_maybe_cell(std::move(value));
  } else if (value.not_null()) {
    stack.push_cell(std::move(value));
    stack.push_bool(true);
  } else {
    stack.push_bool(false);
  }
  return 0;
}

int exec_get_global_common(VmState* st, unsigned n) {
  st->get_stack().push(tuple_extend_index(st->get_c7(), n));
  return 0;
}

int exec_get_global(VmState* st, unsigned args) {
  args &= 31;
  VM_LOG(st) << "execute GETGLOB " << args;
  return exec_get_global_common(st, args);
}

int exec_get_global_var(VmState* st) {
  VM_LOG(st) << "execute GETGLOBVAR";
  st->check_underflow(1);
  unsigned args = st->get_stack().pop_smallint_range(254);
  return exec_get_global_common(st, args);
}

int exec_set_global_common(VmState* st, unsigned idx) {
  Stack& stack = st->get_stack();
  auto x = stack.pop();
  auto tuple = st->get_c7();
  if (idx >= 255) {
    throw VmError{Excno::range_chk, "tuple index out of range"};
  }
  static auto empty_tuple = Ref<Tuple>{true};
  st->set_c7(empty_tuple);  // optimization; use only if no exception can be thrown until true set_c7()
  auto tpay = tuple_extend_set_index(tuple, idx, std::move(x));
  if (tpay > 0) {
    st->consume_tuple_gas(tpay);
  }
  st->set_c7(std::move(tuple));
  return 0;
}

int exec_set_global(VmState* st, unsigned args) {
  args &= 31;
  VM_LOG(st) << "execute SETGLOB " << args;
  st->check_underflow(1);
  return exec_set_global_common(st, args);
}

int exec_set_global_var(VmState* st) {
  VM_LOG(st) << "execute SETGLOBVAR";
  st->check_underflow(2);
  unsigned args = st->get_stack().pop_smallint_range(254);
  return exec_set_global_common(st, args);
}

void register_ton_config_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mkfixedrange(0xf820, 0xf823, 16, 4, instr::dump_1c("GETPARAM "), exec_get_var_param))
      .insert(OpcodeInstr::mksimple(0xf823, 16, "NOW", std::bind(exec_get_param, _1, 3, "NOW")))
      .insert(OpcodeInstr::mksimple(0xf824, 16, "BLOCKLT", std::bind(exec_get_param, _1, 4, "BLOCKLT")))
      .insert(OpcodeInstr::mksimple(0xf825, 16, "LTIME", std::bind(exec_get_param, _1, 5, "LTIME")))
      .insert(OpcodeInstr::mksimple(0xf826, 16, "RANDSEED", std::bind(exec_get_param, _1, 6, "RANDSEED")))
      .insert(OpcodeInstr::mksimple(0xf827, 16, "BALANCE", std::bind(exec_get_param, _1, 7, "BALANCE")))
      .insert(OpcodeInstr::mksimple(0xf828, 16, "MYADDR", std::bind(exec_get_param, _1, 8, "MYADDR")))
      .insert(OpcodeInstr::mksimple(0xf829, 16, "CONFIGROOT", std::bind(exec_get_param, _1, 9, "CONFIGROOT")))
      .insert(OpcodeInstr::mkfixedrange(0xf82a, 0xf830, 16, 4, instr::dump_1c("GETPARAM "), exec_get_var_param))
      .insert(OpcodeInstr::mksimple(0xf830, 16, "CONFIGDICT", exec_get_config_dict))
      .insert(OpcodeInstr::mksimple(0xf832, 16, "CONFIGPARAM", std::bind(exec_get_config_param, _1, false)))
      .insert(OpcodeInstr::mksimple(0xf833, 16, "CONFIGOPTPARAM", std::bind(exec_get_config_param, _1, true)))
      .insert(OpcodeInstr::mksimple(0xf840, 16, "GETGLOBVAR", exec_get_global_var))
      .insert(OpcodeInstr::mkfixedrange(0xf841, 0xf860, 16, 5, instr::dump_1c_and(31, "GETGLOB "), exec_get_global))
      .insert(OpcodeInstr::mksimple(0xf860, 16, "SETGLOBVAR", exec_set_global_var))
      .insert(OpcodeInstr::mkfixedrange(0xf861, 0xf880, 16, 5, instr::dump_1c_and(31, "SETGLOB "), exec_set_global));
}

static constexpr int randseed_idx = 6;

td::RefInt256 generate_randu256(VmState* st) {
  auto tuple = st->get_c7();
  auto t1 = tuple_index(*tuple, 0).as_tuple_range(255);
  if (t1.is_null()) {
    throw VmError{Excno::type_chk, "intermediate value is not a tuple"};
  }
  auto seedv = tuple_index(*t1, randseed_idx).as_int();
  if (seedv.is_null()) {
    throw VmError{Excno::type_chk, "random seed is not an integer"};
  }
  unsigned char seed[32];
  if (!seedv->export_bytes(seed, 32, false)) {
    throw VmError{Excno::range_chk, "random seed out of range"};
  }
  unsigned char hash[64];
  digest::hash_str<digest::SHA512>(hash, seed, 32);
  if (!seedv.write().import_bytes(hash, 32, false)) {
    throw VmError{Excno::range_chk, "cannot store new random seed"};
  }
  td::RefInt256 res{true};
  if (!res.write().import_bytes(hash + 32, 32, false)) {
    throw VmError{Excno::range_chk, "cannot store new random number"};
  }
  static auto empty_tuple = Ref<Tuple>{true};
  st->set_c7(empty_tuple);  // optimization; use only if no exception can be thrown until true set_c7()
  tuple.write()[0].clear();
  t1.write().at(randseed_idx) = std::move(seedv);
  st->consume_tuple_gas(t1);
  tuple.write().at(0) = std::move(t1);
  st->consume_tuple_gas(tuple);
  st->set_c7(std::move(tuple));
  return res;
}

int exec_randu256(VmState* st) {
  VM_LOG(st) << "execute RANDU256";
  st->get_stack().push_int(generate_randu256(st));
  return 0;
}

int exec_rand_int(VmState* st) {
  VM_LOG(st) << "execute RAND";
  auto& stack = st->get_stack();
  stack.check_underflow(1);
  auto x = stack.pop_int_finite();
  auto y = generate_randu256(st);
  typename td::BigInt256::DoubleInt tmp{0};
  tmp.add_mul(*x, *y);
  tmp.rshift(256, -1).normalize();
  stack.push_int(td::make_refint(tmp));
  return 0;
}

int exec_set_rand(VmState* st, bool mix) {
  VM_LOG(st) << "execute " << (mix ? "ADDRAND" : "SETRAND");
  auto& stack = st->get_stack();
  stack.check_underflow(1);
  auto x = stack.pop_int_finite();
  if (!x->unsigned_fits_bits(256)) {
    throw VmError{Excno::range_chk, "new random seed out of range"};
  }
  auto tuple = st->get_c7();
  auto t1 = tuple_index(*tuple, 0).as_tuple_range(255);
  if (t1.is_null()) {
    throw VmError{Excno::type_chk, "intermediate value is not a tuple"};
  }
  if (mix) {
    auto seedv = tuple_index(*t1, randseed_idx).as_int();
    if (seedv.is_null()) {
      throw VmError{Excno::type_chk, "random seed is not an integer"};
    }
    unsigned char buffer[64], hash[32];
    if (!std::move(seedv)->export_bytes(buffer, 32, false)) {
      throw VmError{Excno::range_chk, "random seed out of range"};
    }
    if (!x->export_bytes(buffer + 32, 32, false)) {
      throw VmError{Excno::range_chk, "mixed seed value out of range"};
    }
    digest::hash_str<digest::SHA256>(hash, buffer, 64);
    if (!x.write().import_bytes(hash, 32, false)) {
      throw VmError{Excno::range_chk, "new random seed value out of range"};
    }
  }
  static auto empty_tuple = Ref<Tuple>{true};
  st->set_c7(empty_tuple);  // optimization; use only if no exception can be thrown until true set_c7()
  tuple.write()[0].clear();
  auto tpay = tuple_extend_set_index(t1, randseed_idx, std::move(x));
  if (tpay > 0) {
    st->consume_tuple_gas(tpay);
  }
  tuple.unique_write()[0] = std::move(t1);
  st->consume_tuple_gas(tuple);
  st->set_c7(std::move(tuple));
  return 0;
}

void register_prng_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mksimple(0xf810, 16, "RANDU256", exec_randu256))
      .insert(OpcodeInstr::mksimple(0xf811, 16, "RAND", exec_rand_int))
      .insert(OpcodeInstr::mksimple(0xf814, 16, "SETRAND", std::bind(exec_set_rand, _1, false)))
      .insert(OpcodeInstr::mksimple(0xf815, 16, "ADDRAND", std::bind(exec_set_rand, _1, true)));
}

int exec_compute_hash(VmState* st, int mode) {
  VM_LOG(st) << "execute HASH" << (mode & 1 ? 'S' : 'C') << 'U';
  Stack& stack = st->get_stack();
  std::array<unsigned char, 32> hash;
  if (!(mode & 1)) {
    auto cell = stack.pop_cell();
    hash = cell->get_hash().as_array();
  } else {
    auto cs = stack.pop_cellslice();
    vm::CellBuilder cb;
    CHECK(cb.append_cellslice_bool(std::move(cs)));
    // TODO: use cb.get_hash() instead
    hash = cb.finalize()->get_hash().as_array();
  }
  td::RefInt256 res{true};
  CHECK(res.write().import_bytes(hash.data(), hash.size(), false));
  stack.push_int(std::move(res));
  return 0;
}

template <typename CurveType>
int exec_verify_groth16(VmState* st) {
  using namespace nil::crypto3::algebra;
  using namespace nil::crypto3::zk;

  VM_LOG(st) << "execute VERGRTH16";
  Stack& stack = st->get_stack();
  auto proof_cell = stack.pop_cell();

  CellBuilder cb;
  auto data_cell_proof = cb.store_ref(proof_cell).finalize();
  const unsigned char*  data_cell_proof_data = data_cell_proof->get_data();

  if (data_cell_proof->size() & 7) {
    throw VmError{Excno::cell_und, "Proof DataCell does not consist of an integer number of bytes"};
  }
  
  auto len = (data_cell_proof->size() << 3);
  
  std::vector<unsigned char> data(data_cell_proof_data, data_cell_proof_data + len);

  typename detail::verifier_data_from_bits<snark::r1cs_gg_ppzksnark<CurveType>>::verifier_data verifier_data =
      detail::verifier_data_from_bits<snark::r1cs_gg_ppzksnark<CurveType>>::process(data);

  typename snark::r1cs_gg_ppzksnark<CurveType>::verification_key_type vk(verifier_data.vk);
  typename snark::r1cs_gg_ppzksnark<CurveType>::primary_input_type pi(verifier_data.pi);
  typename snark::r1cs_gg_ppzksnark<CurveType>::proof_type pr(verifier_data.pr);

  stack.push_bool(snark::r1cs_gg_ppzksnark<CurveType>::verify(vk, pi, pr));
  return 0;
}

int exec_compute_sha256(VmState* st) {
  VM_LOG(st) << "execute SHA256U";
  Stack& stack = st->get_stack();
  auto cs = stack.pop_cellslice();
  if (cs->size() & 7) {
    throw VmError{Excno::cell_und, "Slice does not consist of an integer number of bytes"};
  }
  auto len = (cs->size() >> 3);
  unsigned char data[128], hash[32];
  CHECK(len <= sizeof(data));
  CHECK(cs->prefetch_bytes(data, len));
  digest::hash_str<digest::SHA256>(hash, data, len);
  td::RefInt256 res{true};
  CHECK(res.write().import_bytes(hash, 32, false));
  stack.push_int(std::move(res));
  return 0;
}

int exec_ed25519_check_signature(VmState* st, bool from_slice) {
  VM_LOG(st) << "execute CHKSIGN" << (from_slice ? 'S' : 'U');
  Stack& stack = st->get_stack();
  stack.check_underflow(3);
  auto key_int = stack.pop_int();
  auto signature_cs = stack.pop_cellslice();
  unsigned char data[128], key[32], signature[64];
  unsigned data_len;
  if (from_slice) {
    auto cs = stack.pop_cellslice();
    if (cs->size() & 7) {
      throw VmError{Excno::cell_und, "Slice does not consist of an integer number of bytes"};
    }
    data_len = (cs->size() >> 3);
    CHECK(data_len <= sizeof(data));
    CHECK(cs->prefetch_bytes(data, data_len));
  } else {
    auto hash_int = stack.pop_int();
    data_len = 32;
    if (!hash_int->export_bytes(data, data_len, false)) {
      throw VmError{Excno::range_chk, "data hash must fit in an unsigned 256-bit integer"};
    }
  }
  if (!signature_cs->prefetch_bytes(signature, 64)) {
    throw VmError{Excno::cell_und, "Ed25519 signature must contain at least 512 data bits"};
  }
  if (!key_int->export_bytes(key, 32, false)) {
    throw VmError{Excno::range_chk, "Ed25519 public key must fit in an unsigned 256-bit integer"};
  }
  td::Ed25519::PublicKey pub_key{td::SecureString(td::Slice{key, 32})};
  auto res = pub_key.verify_signature(td::Slice{data, data_len}, td::Slice{signature, 64});
  stack.push_bool(res.is_ok() || st->get_chksig_always_succeed());
  return 0;
}

void register_ton_crypto_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  using namespace nil::crypto3::algebra;

  cp0.insert(OpcodeInstr::mksimple(0xf900, 16, "HASHCU", std::bind(exec_compute_hash, _1, 0)))
      .insert(OpcodeInstr::mksimple(0xf901, 16, "HASHSU", std::bind(exec_compute_hash, _1, 1)))
      .insert(OpcodeInstr::mksimple(0xf902, 16, "SHA256U", exec_compute_sha256))
      .insert(OpcodeInstr::mksimple(0xf910, 16, "CHKSIGNU", std::bind(exec_ed25519_check_signature, _1, false)))
      .insert(OpcodeInstr::mksimple(0xf911, 16, "CHKSIGNS", std::bind(exec_ed25519_check_signature, _1, true)))
      .insert(OpcodeInstr::mksimple(0xf912, 16, "VERGRTH16", exec_verify_groth16<curves::mnt4<298>>));
}

int exec_compute_data_size(VmState* st, int mode) {
  VM_LOG(st) << (mode & 2 ? 'S' : 'C') << "DATASIZE" << (mode & 1 ? "Q" : "");
  Stack& stack = st->get_stack();
  stack.check_underflow(2);
  auto bound = stack.pop_int();
  Ref<Cell> cell;
  Ref<CellSlice> cs;
  if (mode & 2) {
    cs = stack.pop_cellslice();
  } else {
    cell = stack.pop_maybe_cell();
  }
  if (!bound->is_valid() || bound->sgn() < 0) {
    throw VmError{Excno::range_chk, "finite non-negative integer expected"};
  }
  VmStorageStat stat{bound->unsigned_fits_bits(63) ? bound->to_long() : (1ULL << 63) - 1};
  bool ok = (mode & 2 ? stat.add_storage(cs.write()) : stat.add_storage(std::move(cell)));
  if (ok) {
    stack.push_smallint(stat.cells);
    stack.push_smallint(stat.bits);
    stack.push_smallint(stat.refs);
  } else if (!(mode & 1)) {
    throw VmError{Excno::cell_ov, "scanned too many cells"};
  }
  if (mode & 1) {
    stack.push_bool(ok);
  }
  return 0;
}

void register_ton_misc_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mksimple(0xf940, 16, "CDATASIZEQ", std::bind(exec_compute_data_size, _1, 1)))
      .insert(OpcodeInstr::mksimple(0xf941, 16, "CDATASIZE", std::bind(exec_compute_data_size, _1, 0)))
      .insert(OpcodeInstr::mksimple(0xf942, 16, "SDATASIZEQ", std::bind(exec_compute_data_size, _1, 3)))
      .insert(OpcodeInstr::mksimple(0xf943, 16, "SDATASIZE", std::bind(exec_compute_data_size, _1, 2)));
}

int exec_load_var_integer(VmState* st, int len_bits, bool sgnd, bool quiet) {
  if (len_bits == 4 && !sgnd) {
    VM_LOG(st) << "execute LDGRAMS" << (quiet ? "Q" : "");
  } else {
    VM_LOG(st) << "execute LDVAR" << (sgnd ? "" : "U") << "INT" << (1 << len_bits) << (quiet ? "Q" : "");
  }
  Stack& stack = st->get_stack();
  auto csr = stack.pop_cellslice();
  td::RefInt256 x;
  int len;
  if (!(csr.write().fetch_uint_to(len_bits, len) && csr.unique_write().fetch_int256_to(len * 8, x, sgnd))) {
    if (quiet) {
      stack.push_bool(false);
    } else {
      throw VmError{Excno::cell_und, "cannot deserialize a variable-length integer"};
    }
  } else {
    stack.push_int(std::move(x));
    stack.push_cellslice(std::move(csr));
    if (quiet) {
      stack.push_bool(true);
    }
  }
  return 0;
}

int exec_store_var_integer(VmState* st, int len_bits, bool sgnd, bool quiet) {
  if (len_bits == 4 && !sgnd) {
    VM_LOG(st) << "execute STGRAMS" << (quiet ? "Q" : "");
  } else {
    VM_LOG(st) << "execute STVAR" << (sgnd ? "" : "U") << "INT" << (1 << len_bits) << (quiet ? "Q" : "");
  }
  Stack& stack = st->get_stack();
  stack.check_underflow(2);
  auto x = stack.pop_int();
  auto cbr = stack.pop_builder();
  unsigned len = ((x->bit_size(sgnd) + 7) >> 3);
  if (len >= (1u << len_bits)) {
    throw VmError{Excno::range_chk};
  }
  if (!(cbr.write().store_long_bool(len, len_bits) && cbr.unique_write().store_int256_bool(*x, len * 8, sgnd))) {
    if (quiet) {
      stack.push_bool(false);
    } else {
      throw VmError{Excno::cell_ov, "cannot serialize a variable-length integer"};
    }
  } else {
    stack.push_builder(std::move(cbr));
    if (quiet) {
      stack.push_bool(true);
    }
  }
  return 0;
}

bool skip_maybe_anycast(CellSlice& cs) {
  if (cs.prefetch_ulong(1) != 1) {
    return cs.advance(1);
  }
  unsigned depth;
  return cs.advance(1)                    // just$1
         && cs.fetch_uint_leq(30, depth)  // anycast_info$_ depth:(#<= 30)
         && depth >= 1                    // { depth >= 1 }
         && cs.advance(depth);            // rewrite_pfx:(bits depth) = Anycast;
}

bool skip_message_addr(CellSlice& cs) {
  switch ((unsigned)cs.fetch_ulong(2)) {
    case 0:  // addr_none$00 = MsgAddressExt;
      return true;
    case 1: {  // addr_extern$01
      unsigned len;
      return cs.fetch_uint_to(9, len)  // len:(## 9)
             && cs.advance(len);       // external_address:(bits len) = MsgAddressExt;
    }
    case 2: {                         // addr_std$10
      return skip_maybe_anycast(cs)   // anycast:(Maybe Anycast)
             && cs.advance(8 + 256);  // workchain_id:int8 address:bits256  = MsgAddressInt;
    }
    case 3: {  // addr_var$11
      unsigned len;
      return skip_maybe_anycast(cs)       // anycast:(Maybe Anycast)
             && cs.fetch_uint_to(9, len)  // addr_len:(## 9)
             && cs.advance(32 + len);     // workchain_id:int32 address:(bits addr_len) = MsgAddressInt;
    }
    default:
      return false;
  }
}

int exec_load_message_addr(VmState* st, bool quiet) {
  VM_LOG(st) << "execute LDMSGADDR" << (quiet ? "Q" : "");
  Stack& stack = st->get_stack();
  auto csr = stack.pop_cellslice(), csr_copy = csr;
  auto& cs = csr.write();
  if (!(skip_message_addr(cs) && csr_copy.write().cut_tail(cs))) {
    csr.clear();
    if (quiet) {
      stack.push_cellslice(std::move(csr_copy));
      stack.push_bool(false);
    } else {
      throw VmError{Excno::cell_und, "cannot load a MsgAddress"};
    }
  } else {
    stack.push_cellslice(std::move(csr_copy));
    stack.push_cellslice(std::move(csr));
    if (quiet) {
      stack.push_bool(true);
    }
  }
  return 0;
}

bool parse_maybe_anycast(CellSlice& cs, StackEntry& res) {
  res = StackEntry{};
  if (cs.prefetch_ulong(1) != 1) {
    return cs.advance(1);
  }
  unsigned depth;
  Ref<CellSlice> pfx;
  if (cs.advance(1)                           // just$1
      && cs.fetch_uint_leq(30, depth)         // anycast_info$_ depth:(#<= 30)
      && depth >= 1                           // { depth >= 1 }
      && cs.fetch_subslice_to(depth, pfx)) {  // rewrite_pfx:(bits depth) = Anycast;
    res = std::move(pfx);
    return true;
  }
  return false;
}

bool parse_message_addr(CellSlice& cs, std::vector<StackEntry>& res) {
  res.clear();
  switch ((unsigned)cs.fetch_ulong(2)) {
    case 0:                                 // addr_none$00 = MsgAddressExt;
      res.emplace_back(td::zero_refint());  // -> (0)
      return true;
    case 1: {  // addr_extern$01
      unsigned len;
      Ref<CellSlice> addr;
      if (cs.fetch_uint_to(9, len)               // len:(## 9)
          && cs.fetch_subslice_to(len, addr)) {  // external_address:(bits len) = MsgAddressExt;
        res.emplace_back(td::make_refint(1));
        res.emplace_back(std::move(addr));
        return true;
      }
      break;
    }
    case 2: {  // addr_std$10
      StackEntry v;
      int workchain;
      Ref<CellSlice> addr;
      if (parse_maybe_anycast(cs, v)             // anycast:(Maybe Anycast)
          && cs.fetch_int_to(8, workchain)       // workchain_id:int8
          && cs.fetch_subslice_to(256, addr)) {  // address:bits256  = MsgAddressInt;
        res.emplace_back(td::make_refint(2));
        res.emplace_back(std::move(v));
        res.emplace_back(td::make_refint(workchain));
        res.emplace_back(std::move(addr));
        return true;
      }
      break;
    }
    case 3: {  // addr_var$11
      StackEntry v;
      int len, workchain;
      Ref<CellSlice> addr;
      if (parse_maybe_anycast(cs, v)             // anycast:(Maybe Anycast)
          && cs.fetch_uint_to(9, len)            // addr_len:(## 9)
          && cs.fetch_int_to(32, workchain)      // workchain_id:int32
          && cs.fetch_subslice_to(len, addr)) {  // address:(bits addr_len) = MsgAddressInt;
        res.emplace_back(td::make_refint(3));
        res.emplace_back(std::move(v));
        res.emplace_back(td::make_refint(workchain));
        res.emplace_back(std::move(addr));
        return true;
      }
      break;
    }
  }
  return false;
}

int exec_parse_message_addr(VmState* st, bool quiet) {
  VM_LOG(st) << "execute PARSEMSGADDR" << (quiet ? "Q" : "");
  Stack& stack = st->get_stack();
  auto csr = stack.pop_cellslice();
  auto& cs = csr.write();
  std::vector<StackEntry> res;
  if (!(parse_message_addr(cs, res) && cs.empty_ext())) {
    if (quiet) {
      stack.push_bool(false);
    } else {
      throw VmError{Excno::cell_und, "cannot parse a MsgAddress"};
    }
  } else {
    stack.push_tuple(std::move(res));
    if (quiet) {
      stack.push_bool(true);
    }
  }
  return 0;
}

// replaces first bits of `addr` with those of `prefix`
Ref<CellSlice> do_rewrite_addr(Ref<CellSlice> addr, Ref<CellSlice> prefix) {
  if (prefix.is_null() || !prefix->size()) {
    return std::move(addr);
  }
  if (prefix->size() > addr->size()) {
    return {};
  }
  if (prefix->size() == addr->size()) {
    return std::move(prefix);
  }
  vm::CellBuilder cb;
  if (!(addr.write().advance(prefix->size()) && cb.append_cellslice_bool(std::move(prefix)) &&
        cb.append_cellslice_bool(std::move(addr)))) {
    return {};
  }
  return vm::load_cell_slice_ref(cb.finalize());
}

int exec_rewrite_message_addr(VmState* st, bool allow_var_addr, bool quiet) {
  VM_LOG(st) << "execute REWRITE" << (allow_var_addr ? "VAR" : "STD") << "ADDR" << (quiet ? "Q" : "");
  Stack& stack = st->get_stack();
  auto csr = stack.pop_cellslice();
  auto& cs = csr.write();
  std::vector<StackEntry> tuple;
  if (!(parse_message_addr(cs, tuple) && cs.empty_ext())) {
    if (quiet) {
      stack.push_bool(false);
      return 0;
    }
    throw VmError{Excno::cell_und, "cannot parse a MsgAddress"};
  }
  int t = (int)std::move(tuple[0]).as_int()->to_long();
  if (t != 2 && t != 3) {
    if (quiet) {
      stack.push_bool(false);
      return 0;
    }
    throw VmError{Excno::cell_und, "cannot parse a MsgAddressInt"};
  }
  auto addr = std::move(tuple[3]).as_slice();
  auto prefix = std::move(tuple[1]).as_slice();
  if (!allow_var_addr) {
    if (addr->size() != 256) {
      if (quiet) {
        stack.push_bool(false);
        return 0;
      }
      throw VmError{Excno::cell_und, "MsgAddressInt is not a standard 256-bit address"};
    }
    td::Bits256 rw_addr;
    td::RefInt256 int_addr{true};
    CHECK(addr->prefetch_bits_to(rw_addr) &&
          (prefix.is_null() || prefix->prefetch_bits_to(rw_addr.bits(), prefix->size())) &&
          int_addr.unique_write().import_bits(rw_addr, false));
    stack.push(std::move(tuple[2]));
    stack.push(std::move(int_addr));
  } else {
    addr = do_rewrite_addr(std::move(addr), std::move(prefix));
    if (addr.is_null()) {
      if (quiet) {
        stack.push_bool(false);
        return 0;
      }
      throw VmError{Excno::cell_und, "cannot rewrite address in a MsgAddressInt"};
    }
    stack.push(std::move(tuple[2]));
    stack.push(std::move(addr));
  }
  if (quiet) {
    stack.push_bool(true);
  }
  return 0;
}

void register_ton_currency_address_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mksimple(0xfa00, 16, "LDGRAMS", std::bind(exec_load_var_integer, _1, 4, false, false)))
      .insert(OpcodeInstr::mksimple(0xfa01, 16, "LDVARINT16", std::bind(exec_load_var_integer, _1, 4, true, false)))
      .insert(OpcodeInstr::mksimple(0xfa02, 16, "STGRAMS", std::bind(exec_store_var_integer, _1, 4, false, false)))
      .insert(OpcodeInstr::mksimple(0xfa03, 16, "STVARINT16", std::bind(exec_store_var_integer, _1, 4, true, false)))
      .insert(OpcodeInstr::mksimple(0xfa04, 16, "LDVARUINT32", std::bind(exec_load_var_integer, _1, 5, false, false)))
      .insert(OpcodeInstr::mksimple(0xfa05, 16, "LDVARINT32", std::bind(exec_load_var_integer, _1, 5, true, false)))
      .insert(OpcodeInstr::mksimple(0xfa06, 16, "STVARUINT32", std::bind(exec_store_var_integer, _1, 5, false, false)))
      .insert(OpcodeInstr::mksimple(0xfa07, 16, "STVARINT32", std::bind(exec_store_var_integer, _1, 5, true, false)))
      .insert(OpcodeInstr::mksimple(0xfa40, 16, "LDMSGADDR", std::bind(exec_load_message_addr, _1, false)))
      .insert(OpcodeInstr::mksimple(0xfa41, 16, "LDMSGADDRQ", std::bind(exec_load_message_addr, _1, true)))
      .insert(OpcodeInstr::mksimple(0xfa42, 16, "PARSEMSGADDR", std::bind(exec_parse_message_addr, _1, false)))
      .insert(OpcodeInstr::mksimple(0xfa43, 16, "PARSEMSGADDRQ", std::bind(exec_parse_message_addr, _1, true)))
      .insert(
          OpcodeInstr::mksimple(0xfa44, 16, "REWRITESTDADDR", std::bind(exec_rewrite_message_addr, _1, false, false)))
      .insert(
          OpcodeInstr::mksimple(0xfa45, 16, "REWRITESTDADDRQ", std::bind(exec_rewrite_message_addr, _1, false, true)))
      .insert(
          OpcodeInstr::mksimple(0xfa46, 16, "REWRITEVARADDR", std::bind(exec_rewrite_message_addr, _1, true, false)))
      .insert(
          OpcodeInstr::mksimple(0xfa47, 16, "REWRITEVARADDRQ", std::bind(exec_rewrite_message_addr, _1, true, true)));
}

static constexpr int output_actions_idx = 5;

int install_output_action(VmState* st, Ref<Cell> new_action_head) {
  // TODO: increase actions:uint16 and msgs_sent:uint16 in SmartContractInfo at first reference of c5
  VM_LOG(st) << "installing an output action";
  st->set_d(output_actions_idx, std::move(new_action_head));
  return 0;
}

static inline Ref<Cell> get_actions(VmState* st) {
  return st->get_d(output_actions_idx);
}

int exec_send_raw_message(VmState* st) {
  VM_LOG(st) << "execute SENDRAWMSG";
  Stack& stack = st->get_stack();
  stack.check_underflow(2);
  int f = stack.pop_smallint_range(255);
  Ref<Cell> msg_cell = stack.pop_cell();
  CellBuilder cb;
  if (!(cb.store_ref_bool(get_actions(st))     // out_list$_ {n:#} prev:^(OutList n)
        && cb.store_long_bool(0x0ec3c86d, 32)  // action_send_msg#0ec3c86d
        && cb.store_long_bool(f, 8)            // mode:(## 8)
        && cb.store_ref_bool(std::move(msg_cell)))) {
    throw VmError{Excno::cell_ov, "cannot serialize raw output message into an output action cell"};
  }
  return install_output_action(st, cb.finalize());
}

bool store_grams(CellBuilder& cb, td::RefInt256 value) {
  int k = value->bit_size(false);
  return k <= 15 * 8 && cb.store_long_bool((k + 7) >> 3, 4) && cb.store_int256_bool(*value, (k + 7) & -8, false);
}

int exec_reserve_raw(VmState* st, int mode) {
  VM_LOG(st) << "execute RAWRESERVE" << (mode & 1 ? "X" : "");
  Stack& stack = st->get_stack();
  stack.check_underflow(2 + (mode & 1));
  int f = stack.pop_smallint_range(15);
  Ref<Cell> y;
  if (mode & 1) {
    y = stack.pop_maybe_cell();
  }
  auto x = stack.pop_int_finite();
  if (td::sgn(x) < 0) {
    throw VmError{Excno::range_chk, "amount of nanograms must be non-negative"};
  }
  CellBuilder cb;
  if (!(cb.store_ref_bool(get_actions(st))     // out_list$_ {n:#} prev:^(OutList n)
        && cb.store_long_bool(0x36e6b809, 32)  // action_reserve_currency#36e6b809
        && cb.store_long_bool(f, 8)            // mode:(## 8)
        && store_grams(cb, std::move(x))       //
        && cb.store_maybe_ref(std::move(y)))) {
    throw VmError{Excno::cell_ov, "cannot serialize raw reserved currency amount into an output action cell"};
  }
  return install_output_action(st, cb.finalize());
}

int exec_set_code(VmState* st) {
  VM_LOG(st) << "execute SETCODE";
  auto code = st->get_stack().pop_cell();
  CellBuilder cb;
  if (!(cb.store_ref_bool(get_actions(st))         // out_list$_ {n:#} prev:^(OutList n)
        && cb.store_long_bool(0xad4de08e, 32)      // action_set_code#ad4de08e
        && cb.store_ref_bool(std::move(code)))) {  // new_code:^Cell = OutAction;
    throw VmError{Excno::cell_ov, "cannot serialize new smart contract code into an output action cell"};
  }
  return install_output_action(st, cb.finalize());
}

int exec_set_lib_code(VmState* st) {
  VM_LOG(st) << "execute SETLIBCODE";
  Stack& stack = st->get_stack();
  stack.check_underflow(2);
  int mode = stack.pop_smallint_range(2);
  auto code = stack.pop_cell();
  CellBuilder cb;
  if (!(cb.store_ref_bool(get_actions(st))         // out_list$_ {n:#} prev:^(OutList n)
        && cb.store_long_bool(0x26fa1dd4, 32)      // action_change_library#26fa1dd4
        && cb.store_long_bool(mode * 2 + 1, 8)     // mode:(## 7) { mode <= 2 }
        && cb.store_ref_bool(std::move(code)))) {  // libref:LibRef = OutAction;
    throw VmError{Excno::cell_ov, "cannot serialize new library code into an output action cell"};
  }
  return install_output_action(st, cb.finalize());
}

int exec_change_lib(VmState* st) {
  VM_LOG(st) << "execute CHANGELIB";
  Stack& stack = st->get_stack();
  stack.check_underflow(2);
  int mode = stack.pop_smallint_range(2);
  auto hash = stack.pop_int_finite();
  if (!hash->unsigned_fits_bits(256)) {
    throw VmError{Excno::range_chk, "library hash must be non-negative"};
  }
  CellBuilder cb;
  if (!(cb.store_ref_bool(get_actions(st))             // out_list$_ {n:#} prev:^(OutList n)
        && cb.store_long_bool(0x26fa1dd4, 32)          // action_change_library#26fa1dd4
        && cb.store_long_bool(mode * 2, 8)             // mode:(## 7) { mode <= 2 }
        && cb.store_int256_bool(hash, 256, false))) {  // libref:LibRef = OutAction;
    throw VmError{Excno::cell_ov, "cannot serialize library hash into an output action cell"};
  }
  return install_output_action(st, cb.finalize());
}

void register_ton_message_ops(OpcodeTable& cp0) {
  using namespace std::placeholders;
  cp0.insert(OpcodeInstr::mksimple(0xfb00, 16, "SENDRAWMSG", exec_send_raw_message))
      .insert(OpcodeInstr::mksimple(0xfb02, 16, "RAWRESERVE", std::bind(exec_reserve_raw, _1, 0)))
      .insert(OpcodeInstr::mksimple(0xfb03, 16, "RAWRESERVEX", std::bind(exec_reserve_raw, _1, 1)))
      .insert(OpcodeInstr::mksimple(0xfb04, 16, "SETCODE", exec_set_code))
      .insert(OpcodeInstr::mksimple(0xfb06, 16, "SETLIBCODE", exec_set_lib_code))
      .insert(OpcodeInstr::mksimple(0xfb07, 16, "CHANGELIB", exec_change_lib));
}

void register_ton_ops(OpcodeTable& cp0) {
  register_basic_gas_ops(cp0);
  register_ton_gas_ops(cp0);
  register_prng_ops(cp0);
  register_ton_config_ops(cp0);
  register_ton_crypto_ops(cp0);
  register_ton_misc_ops(cp0);
  register_ton_currency_address_ops(cp0);
  register_ton_message_ops(cp0);
}

}  // namespace vm
