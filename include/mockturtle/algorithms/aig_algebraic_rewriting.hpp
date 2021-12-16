/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
      : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{ true }; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n )
                        {
                          if ( try_algebraic_rules( n ) )
                          {
                            ntk.update_levels();
                            cont = true;
                          }
                        } );
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */
    if ( try_three_layers_distributivity( n ) )
      return true;

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    /* TODO */
    //return false;

    bool level_zero = false;    //to check that the children of the node are not both on level zero
    bool child_on_crit_path = false; //it goes to true if one child is on the critical path --> if both signals are on the critical path the property should not be applied
    bool substitution = false;
    bool associativity_not_ok = false;
    bool first_child = false;

    signal snode_gran_critical; //node on the critical path where the AND should be removed
    signal snode_grand_to_move; //the other node that needs to be moved in another AND gate
    signal snode_child_to_move; //child node that needs to be added to the new AND gate

    uint32_t level_1 = 0;
    uint32_t level_2 = 0;

    if ( ntk.is_on_critical_path( n ) )
    {
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           node node_child = ntk.get_node( s );
                           signal signal_child = s;

                           /* if ( ntk.level( node_child ) == 0 && level_zero == false )
                             level_zero = true;
                           else if ( ntk.level( node_child ) == 0 && level_zero == true )
                           {
                             associativity_not_ok = true;
                             return false; //both children are on the level zero, so the operation cannot be done
                           }*/

                           if ( first_child == false )
                           {
                             level_1 = ntk.level( node_child );
                             first_child = true;
                           }
                           else
                           {
                             level_2 = ntk.level( node_child );
                             if ( level_1 >= level_2 - 1 && level_1 <= level_2 + 1 )
                             {
                               associativity_not_ok = true;
                               return;
                             }
                           }

                           if ( ntk.is_on_critical_path( node_child ) )
                           {                                    //evaluated only if it is on the critical path
                             if ( child_on_crit_path == false ) //to check if both children on the critical path
                               child_on_crit_path = true;
                             else
                             {
                               associativity_not_ok = true;
                               return; // if both children are on critical path no operation is applied
                             }

                             if ( ntk.level( node_child ) != 0 )
                             {
                               if ( !( ntk.is_complemented( signal_child ) ) )
                               {
                                 ntk.foreach_fanin( node_child, [&]( signal const& f )
                                                    {
                                                      node node_granchild = ntk.get_node( f );
                                                      signal signal_grandchild = f;
                                         
                                                      if ( ntk.is_on_critical_path( node_granchild ))
                                                      {
                                                        if ( substitution == false ) //the first grnachild detected on the critical path is saved to be later moved while the other will be put in the new AND 
                                                        {
                                                            snode_gran_critical = signal_grandchild;
                                                            substitution = true;
                                                        }
                                                        else
                                                        {
                                                            associativity_not_ok = true;
                                                            return;
                                                        }
                                                      }
                                                      else // if the granchild is not on the critical path it will be moved or if the grandchild is evaluated after the other which is on the critical path
                                                        {
                                                        snode_grand_to_move = signal_grandchild;
                                                      }                                                    
                                                    } );
                               }
                               else
                               {
                                 associativity_not_ok = true;
                                 return; // if the node is on the critical path and it is complemented the operation cannot be done
                               }
                             }
                             else
                             {
                               associativity_not_ok = true;
                               return; //if the node is a PI and it is on the critical path, the operation cannot be applied
                             }
                           }
                           else
                           {
                             snode_child_to_move = signal_child;
                           }
      } );
    }
    else
    {
      return false;
    }

    if ( associativity_not_ok == true )
    {
      return false;
    }
    
    if ( substitution == true )
    {                                                                                     //creation of the new 2 AND and removal of the old ones
      signal new_and_signal = ntk.create_and( snode_child_to_move, snode_grand_to_move ); //creation of new AND node
      signal updated_and = ntk.create_and( new_and_signal, snode_gran_critical );
      ntk.substitute_node( n, updated_and );
      return true;
    }
    
    return false;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    /* TODO */
    // return false;
    bool first_child_evaluation = false; //to save the first pair of grandchild to be compared with the other two
    bool flag_child1 = false;            //to know which operand the code is looking at + correct saving
    bool flag_child2 = false;
    bool distributivity_not_ok = false;

    bool sharing = false; //to know lated if there is a common node in the critical path

    signal signal_gran_shared, signal_not_crit_child2; //signal to be saved to create the new netlist later (the common signal and the other one of the second child)

    signal first_gran_op1, first_gran_op2; //the two operands of the first evaluated child

    node test;

    if ( ntk.is_on_critical_path( n ) )
    {
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           node node_child = ntk.get_node( s );
                           signal signal_child = s;

                           if ( ntk.level( node_child ) == 0 )
                           {
                             distributivity_not_ok = true;
                             return false; //if at least one child is at level zero the operation cannot be performed
                           }

                           if ( ntk.is_on_critical_path( node_child ) )
                           { //evaluated only if it is on the critical path

                             if ( ntk.is_complemented( signal_child ) )
                             {
                               ntk.foreach_fanin( node_child, [&]( signal const& f )
                                                  {
                                                    node node_granchild = ntk.get_node( f );
                                                    signal signal_grandchild = f;
                                                    if ( flag_child1 == false )
                                                    { //saving of the first two signals implied in the first evaluated AND
                                                      first_gran_op1 = signal_grandchild;
                                                      flag_child1 = true;
                                                    }
                                                    else if ( flag_child1 == true && first_child_evaluation == false )
                                                    {
                                                      first_gran_op2 = signal_grandchild;
                                                      first_child_evaluation = true;
                                                    }
                                                    else if ( first_child_evaluation == true )
                                                    {
                                                      if ( ( signal_grandchild == first_gran_op1 || signal_grandchild == first_gran_op2 ) && sharing == false )
                                                      {
                                                        if ( ntk.is_on_critical_path( node_granchild ) )
                                                        {
                                                          signal_gran_shared = signal_grandchild;
                                                          sharing = true;
                                                        }
                                                        else
                                                        {
                                                          distributivity_not_ok = true;
                                                          return false;
                                                        }
                                                      }
                                                      else
                                                        signal_not_crit_child2 = signal_grandchild;
                                                    }
                                                    else
                                                    {
                                                      distributivity_not_ok = true;
                                                      return false;
                                                    }
                                                  } );
                             }
                             else
                             {
                               distributivity_not_ok = true;
                               return false; // if the node is on the critical path and it is NOT complemented the operation cannot be done
                             }
                           }
                           else
                           {
                             distributivity_not_ok = true;
                             return false; //if one child is not on the critical path they are not sharing the common signal on the critical path and the opeation cannot be evaluated
                           }
                         } );
    }
    else
    {
      return false;
    }

    if ( distributivity_not_ok == true )
    {
      return false;
    }
    else if ( sharing == true )
    { //creation of the new 2 AND and removal of the old ones
      if ( signal_gran_shared == first_gran_op1 )
      {
        if ( !ntk.is_on_critical_path( ntk.get_node( first_gran_op2 ) ) && !ntk.is_on_critical_path( ntk.get_node( signal_not_crit_child2 ) ) )
        {
          signal new_and_not_critical = ntk.create_and( !first_gran_op2, !signal_not_crit_child2 );
          signal updated_and = ntk.create_and( first_gran_op1, !new_and_not_critical );
          ntk.substitute_node( n, !updated_and );
          //creazione AND con gli altri due operandi con gli ingressi complementati rispetto ad adesso
          //creazione AND del nodo padre dal op1 e dal complementato della porta
          //sostituzione delle due AND
          //complemento segnale in uscita
          return true;
        }
        else
        {
          return false;
        }
      }
      else if ( signal_gran_shared == first_gran_op2 )
      {
        if ( !ntk.is_on_critical_path( ntk.get_node( first_gran_op1 ) ) && !ntk.is_on_critical_path( ntk.get_node( signal_not_crit_child2 ) ) )
        {
          signal new_and_not_critical = ntk.create_and( !first_gran_op1, !signal_not_crit_child2 );
          signal updated_and = ntk.create_and( first_gran_op2, !new_and_not_critical );
          ntk.substitute_node( n, !updated_and );
          return true;
        }
        else
        {
          return false;
        }
      }
      else
        return false;
    }
    return false;
  }

  bool try_three_layers_distributivity( node n )
  {
    //return false;
    bool first_layer_level = false; //to save the first layer level to be compared with the one on the critical path. It is advantageous only if it is smaller of at least 4 units
    bool second_layer_level = false; //this gest true when the node x3 has been analyzed --> not on critical path
    bool rule_not_ok = false;        //this gest true in any case this realtion cannot be applicable
    bool substitution = false;       //check when the condition to apply the rule is
    bool crit1 = false;
    bool crit2 = false;


    signal signal_x4;
    signal signal_x3;
    signal signal_x2;
    signal signal_crit;

    //to check the two child level signals --> they difference should be at least 3 to avoid to modify the critical path
    uint32_t level_crit = 0;
    uint32_t level_non_crit = 0;

    if ( ntk.is_on_critical_path( n ) )
    {
      ntk.foreach_fanin( n, [&]( signal const& f )
                         {
                           node node_layer_1 = ntk.get_node( f );
                           signal s_layer_1 = f;

                           if ( !ntk.is_on_critical_path( node_layer_1 ) ) //save the detail of the node x4 that needs to be moved of 4 steps
                           {
                             signal_x4 = s_layer_1;
                             level_non_crit = ntk.level( node_layer_1 );
                           }
                           else if ( ntk.is_on_critical_path( node_layer_1 ) && crit1 == false ) //crit1 to check that there are not two children both on critical path
                           {
                             crit1 = true;
                             level_crit = ntk.level( node_layer_1 );
                             if ( ntk.is_complemented( s_layer_1 ) )
                             {
                               ntk.foreach_fanin( node_layer_1, [&]( signal const& s )
                                                  {
                                                    node node_layer_2 = ntk.get_node( s );
                                                    signal s_layer_2 = s;
                                                    if ( !ntk.is_on_critical_path( node_layer_2 ) )
                                                    {
                                                      signal_x3 = s_layer_2;
                                                      //second_layer_level = true;
                                                    }
                                                    else if ( ntk.is_on_critical_path( node_layer_2 ) && crit2 == false )
                                                    {
                                                      crit2 = true;
                                                      if ( ntk.is_complemented( s_layer_2 ) )
                                                      {
                                                        ntk.foreach_fanin( node_layer_2, [&]( signal const& k )
                                                                           {
                                                                             node node_layer_3 = ntk.get_node( k );
                                                                             signal s_layer_3 = k;

                                                                             if ( ntk.is_on_critical_path( node_layer_3 ) )
                                                                             {
                                                                               signal_crit = s_layer_3;

                                                                               if ( substitution == false )
                                                                               {
                                                                                 substitution = true;
                                                                               }
                                                                               else
                                                                               {
                                                                                 rule_not_ok = true; //if both are on critical path the rule is not applicable and convenient
                                                                                 return;
                                                                               }                                                                                
                                                                             }                                                                            
                                                                             else 
                                                                             {
                                                                               signal_x2 = s_layer_3;
                                                                               
                                                                             }

                                                                           } );
                                                      }
                                                      else
                                                      {
                                                        rule_not_ok = true;
                                                        return;
                                                      }
                                                    }
                                                    else
                                                    {
                                                      rule_not_ok = true;
                                                      return;
                                                    }
                                                  } );
                             }
                             else //if the node is on the critical path, but it is not complemented the following gate is not a OR, so the rule is not applicable
                             {
                               rule_not_ok = true;
                               return;
                             }
                           }
                           else
                           {
                             rule_not_ok = true;
                             return;
                           }
                         } );
    }
    else
    {
      return false;
    }

    if ( level_crit - level_non_crit < 3 )
    {
      rule_not_ok = true;
      return false;
    }

    if ( rule_not_ok == true )
    {
      return false; //rule not applicable
    }

    if ( substitution == true )
    {
      signal and_x3x4 = ntk.create_and( !signal_x3, signal_x4 );
      signal and_x2x4 = ntk.create_and( signal_x2, signal_x4 );
      signal and_crit = ntk.create_and( signal_crit, and_x2x4 );
      signal updated_and = ntk.create_and( !and_x3x4, !and_crit );
      ntk.substitute_node( n, !updated_and );
      return true;
    }
    
    return false;
  }

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ ntk };
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */