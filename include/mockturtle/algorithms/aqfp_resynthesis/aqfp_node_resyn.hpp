/* mockturtle: C++ logic network library
 * Copyright (C) 2018-2021  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file aqfp_node_resyn.hpp
  \brief AQFP node resynthesis strategy

  \author Dewmini Marakkalage 
*/

#pragma once

#include "../../traits.hpp"

#include "./aqfp_db.hpp"

#include <type_traits>
#include <unordered_map>
#include <vector>

namespace mockturtle
{

/*! \brief Strategy for resynthesizing a node.
 *
 * cost_based  - choose the database entry that gives the minimum cost and break ties uing the level
 * level_based - choose the database entry that gives the minimum level and break ties uing the cost
 */
enum class aqfp_node_resyn_strategy
{
  cost_based,
  level_based
};

/*! \brief Parameters for aqfp_node_resyn. */
struct aqfp_node_resyn_param
{
  std::unordered_map<uint32_t, double> splitters;
  aqfp_node_resyn_strategy strategy = aqfp_node_resyn_strategy::cost_based;
  bool branch_pis;
};

/*! \brief This datastructure can be passed to `aqfp_resynthesis` as the node resynthesis algorithm. */
struct aqfp_node_resyn
{
  aqfp_node_resyn( aqfp_db<>& db, const aqfp_node_resyn_param& ps ) : params( ps ), db( db )
  {
  }

  template<typename NtkDest, typename TruthTable, typename LeavesIterator, typename LevelUpdateCallback, typename ResynPerformedCallback>
  void operator()( NtkDest& ntk_dest, const TruthTable& f, LeavesIterator leaves_begin, LeavesIterator leaves_end,
                   LevelUpdateCallback&& level_update_callback, ResynPerformedCallback&& resyn_performed_callback )
  {
    static_assert( std::is_invocable_v<LevelUpdateCallback, node<NtkDest>, uint32_t>,
                   "LevelUpdateCallback must be callable with arguments of types (node<NtkDest>, level)" );
    static_assert( std::is_invocable_v<ResynPerformedCallback, signal<NtkDest>, uint32_t>,
                   "ResynPerformedCallback must be callable with arguments of type (signal<NtkDest>, level)" );

    std::vector<signal<NtkDest>> leaves;
    std::vector<uint32_t> leaf_levels;
    std::vector<bool> leaf_no_splitters;
    for ( auto it = leaves_begin; it != leaves_end; it++ )
    {
      auto leaf = std::get<0>( *it );
      auto leaf_level = std::get<1>( *it );

      leaves.push_back( leaf );
      leaf_levels.push_back( leaf_level );
      leaf_no_splitters.push_back( ntk_dest.is_constant( ntk_dest.get_node( leaf ) ) || ( ntk_dest.is_ci( ntk_dest.get_node( leaf ) ) && !params.branch_pis));
    }

    // should not have more than 4 fanin nodes
    assert( leaves.size() <= 4u );

    // if less than 4 fanins, add dummy inputs
    while ( leaves.size() < 4u )
    {
      leaves.push_back( ntk_dest.get_constant( false ) );
      leaf_levels.push_back( 0u );
      leaf_no_splitters.push_back( true );
    }

    auto tt = kitty::extend_to( f, 4u );

    auto new_n = ntk_dest.get_constant( false );
    auto n_lev = 0u;
    switch ( tt._bits[0] )
    {
    case 0x0000u:
      new_n = ntk_dest.get_constant( false );
      break;
    case 0xffffu:
      new_n = ntk_dest.get_constant( true );
      break;
    case 0x5555u:
      new_n = !leaves[0];
      n_lev = leaf_levels[0];
      break;
    case 0xaaaau:
      new_n = leaves[0];
      n_lev = leaf_levels[0];
      break;
    case 0x3333u:
      new_n = !leaves[1];
      n_lev = leaf_levels[1];
      break;
    case 0xccccu:
      new_n = leaves[1];
      n_lev = leaf_levels[1];
      break;
    case 0x0f0fu:
      new_n = !leaves[2];
      n_lev = leaf_levels[2];
      break;
    case 0xf0f0u:
      new_n = leaves[2];
      n_lev = leaf_levels[2];
      break;
    case 0x00ffu:
      new_n = !leaves[3];
      n_lev = leaf_levels[3];
      break;
    case 0xff00u:
      new_n = leaves[3];
      n_lev = leaf_levels[3];
      break;
    default:
      auto [mig, depths, output_inv] = db.get_best_replacement(
          tt._bits[0], leaf_levels, leaf_no_splitters,
          [&]( const std::pair<double, uint32_t>& f, const std::pair<double, uint32_t>& s ) {
            if ( params.strategy == aqfp_node_resyn_strategy::cost_based )
            {
              return ( f.first < s.first || ( f.first == s.first && f.second < s.second ) );
            }
            else
            {
              return ( f.second < s.second || ( f.second == s.second && f.first < s.first ) );
            }
          } );

      std::vector<signal<NtkDest>> sig_map( mig.size() );
      std::vector<uint32_t> lev_map( mig.size() );

      sig_map[0] = ntk_dest.get_constant( false );
      lev_map[0] = 0u;
      for ( auto i = 1u; i <= 4u; i++ )
      {
        sig_map[i] = leaves[i - 1];
        lev_map[i] = leaf_levels[i - 1];
      }
      for ( auto i = 5u; i < mig.size(); i++ )
      {
        std::vector<signal<NtkDest>> fanin;
        for ( auto fin : mig[i] )
        {
          const auto fin_inv = ( ( fin & 1u ) == 1u );
          const auto fin_id = ( fin >> 1 );
          fanin.push_back( fin_inv ? !sig_map[fin_id] : sig_map[fin_id] );
        }
        sig_map[i] = ntk_dest.create_maj( fanin );
        lev_map[i] = 0u;

        const auto node_i = ntk_dest.get_node( sig_map[i] );
        if ( !( ntk_dest.is_constant( node_i ) || ntk_dest.is_ci( node_i ) ) )
        {
          for ( auto fin : mig[i] )
          {
            const auto fin_id = ( fin >> 1u );
            const auto lev_dif = ( depths[fin_id] > depths[i] ) ? depths[fin_id] - depths[i] : 1u;
            lev_map[i] = std::max( lev_map[i], lev_map[fin_id] + lev_dif );
          }
        }

        level_update_callback( ntk_dest.get_node( sig_map[i] ), lev_map[i] );
      }
      n_lev = lev_map[mig.size() - 1];
      new_n = output_inv ? !sig_map[mig.size() - 1] : sig_map[mig.size() - 1];
    }

    resyn_performed_callback( new_n, n_lev );
  }

private:
  aqfp_node_resyn_param params;
  aqfp_db<>& db;
};

} // namespace mockturtle
