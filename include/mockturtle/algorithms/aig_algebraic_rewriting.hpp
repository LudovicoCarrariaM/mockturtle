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
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity_or( n ) )
      return true;
    /* TODO: add more rules here... */
    if ( try_distributivity_and( n ) )
      return true;

    if (try_TL_distributivity(n))
      return true;
    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    /* TODO */
    if ( ntk.is_on_critical_path( n ) )
    {
      std::vector<node> children_n;
      std::vector<signal> grandchildren, children_s;
      signal and_low, and_high;
      ntk.foreach_fanin( n, [&]( signal const& child )
                         {
                           children_n.emplace_back( ntk.get_node( child ) );
                           children_s.emplace_back( child );
                         } );
      if ( ntk.level( children_n[0] ) > ntk.level( children_n[1] ) )
      {
        std::swap( children_s[0], children_s[1] );
        std::swap( children_n[0], children_n[1] );
      } //have child 1 be on crit path
      if ( (ntk.level( children_n[0] ) == ntk.level( children_n[1] ) ) || ntk.is_complemented(children_s[1]))
        return false; //check that children have different level and the one on crit path isn't a NAND
      else
      {
        ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild ) { 
            grandchildren.emplace_back( grandchild );
        } );
        if ( ntk.level( ntk.get_node( grandchildren[0] ) ) > ntk.level(ntk.get_node(grandchildren[1])))
        {
          std::swap( grandchildren[0], grandchildren[1] );
        } //have grandchild 1 be on crit path
        if ( ntk.level( ntk.get_node( grandchildren[0] ) ) == ntk.level( ntk.get_node( grandchildren[1] ) ) )
          return false; //check if grandchildren aren't on the same path
        if ( ntk.level( children_n[0] ) < ntk.level( ntk.get_node( grandchildren[1] ) ) )
        {
          //child 1 on crit path, grandchild 1 on crit path =>
          and_low = ntk.create_and( grandchildren[0], children_s[0] );
          and_high = ntk.create_and( and_low, grandchildren[1] );
          ntk.substitute_node( n, and_high );
          return true;
        }
        else
          return false;
      }
    }
    else
      return false;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity_or( node n )
  {

    /* TODO */
    if ( ntk.is_on_critical_path( n ) )
    {
      std::vector<node> children_n;
      std::vector<signal> others, children_s;
      signal and_low, and_high, shared_child;
      bool found = false;
      bool crit = false;
      bool flag = false;
      ntk.foreach_fanin( n, [&]( signal const& child )
                         {
                           children_n.emplace_back( ntk.get_node( child ) );
                           children_s.emplace_back( child );
                           if ( !ntk.is_on_critical_path( ntk.get_node( child ) ) )
                           {
                             crit = true;
                           }
                           if ( !ntk.is_complemented( child ) )
                           {
                             flag = true;
                           }
                         } );
      if ( flag || crit )
        return false;
      
      if ( children_n.size() < 2 )
      {
        return false;
      }
      ntk.foreach_fanin( children_n[0], [&]( signal const& grandchild2 ){
        ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild3){ 
          if ( (grandchild2 == grandchild3 ) && ntk.is_on_critical_path( ntk.get_node( grandchild2 ) ) ){
             found = true;
             shared_child = grandchild2;
          }      
        } );
      } );
      if ( found ){
        ntk.foreach_fanin( children_n[0], [&]( signal const& grandchild4 ){
          if ( ( grandchild4 != shared_child ) && !ntk.is_on_critical_path( ntk.get_node( grandchild4 ) ) ){
            others.emplace_back( grandchild4 );
          }
        } );
        ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild5 ){
           if ( ( (grandchild5) != shared_child ) && !ntk.is_on_critical_path( ntk.get_node( grandchild5 ) ) ){
             others.emplace_back( grandchild5 );
           }
        } );
        if ( others.size() < 2 )
        {
          return false;
        }
        else
        {
          and_low = !ntk.create_and( !others[0], !others[1] );
          and_high = ntk.create_and( and_low, shared_child );
          ntk.substitute_node( n, !and_high );
          return true;
        }
      }
      else
        return false;
          
    }
    else
      return false;

      
  }

  bool try_distributivity_and(node n) {
    if ( ntk.is_on_critical_path( n ) )
    {
      std::vector<node> children_n;
      std::vector<signal> others, children_s;
      signal and_low, and_high, shared_child;
      bool found = false;
      ntk.foreach_fanin( n, [&]( signal const& child )
                         {
                           children_n.emplace_back( ntk.get_node( child ) );
                           children_s.emplace_back( child );
                           if ( !ntk.is_on_critical_path( ntk.get_node( child ) ) )
                             return false;
                           if ( ntk.is_complemented( child ) )
                             return false;
                         } );
      if ( children_n.size() != 2 )
        return false;
      ntk.foreach_fanin( children_n[0], [&]( signal const& grandchild0 )
                         {
                           ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild1 )
                                              {
                                                if ( ( grandchild0 == grandchild1 ) && ntk.is_on_critical_path( ntk.get_node( grandchild0 ) ) )
                                                {
                                                  found = true;
                                                  shared_child = grandchild0;
                                                }
                                              } );
                         } );
      if ( found )
      {
        ntk.foreach_fanin( children_n[0], [&]( signal const& grandchild0 )
                           {
                             if ( ( grandchild0 != shared_child ) && !ntk.is_on_critical_path( ntk.get_node( grandchild0 ) ) )
                             {
                               others.emplace_back( grandchild0 );
                             }
                           } );
        ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild1 )
                           {
                             if ( ( grandchild1 != shared_child ) && !ntk.is_on_critical_path( ntk.get_node( grandchild1 ) ) )
                             {
                               others.emplace_back( grandchild1 );
                             }
                           } );
        if ( others.size() != 2 )
          return false;
        else
        {
          and_low = ntk.create_and( others[0], others[1] );
          and_high = ntk.create_and( and_low, shared_child );
          ntk.substitute_node( n, and_high );
          return true;
        }
      }
      else
        return false;
    }
    else
      return false;


  }
  bool try_TL_distributivity(node n)
  {
    if (ntk.is_on_critical_path( n ))
      {
        std::vector<node> children_n, grandchildren_n;
        std::vector<signal> grandchildren_s, children_s, grandgrandchildren;
        signal and_middle, and_up, and_left, and_right;
        ntk.foreach_fanin( n, [&]( signal const& child )
                           {
                             children_n.emplace_back( ntk.get_node( child ) );
                             children_s.emplace_back( child );
                           } );
        if ( children_s.size() != 2 )
          return false;
        if ( ntk.level( children_n[0] ) > ntk.level( children_n[1] ) )
        {
          std::swap( children_s[0], children_s[1] );
          std::swap( children_n[0], children_n[1] );
        } //have child 1 be on crit path
        if ( ntk.level( children_n[0] ) == ntk.level( children_n[1] ) )
          return false; //can't do anything if both on critical path
        if ( !ntk.is_complemented( children_s[1] ) )
          return false;
        if ( ntk.is_on_critical_path( children_n[0] ) )
          return false;
        
        ntk.foreach_fanin( children_n[1], [&]( signal const& grandchild )
                             {
                               grandchildren_s.emplace_back( grandchild );
                               grandchildren_n.emplace_back( ntk.get_node( grandchild ) );
                             } );
        if ( grandchildren_s.size() != 2 )
            return false;
        
        if ( ntk.level( grandchildren_n[0] ) > ntk.level( grandchildren_n[1] ) )
          {
            std::swap( grandchildren_n[0], grandchildren_n[1] );
            std::swap( grandchildren_s[0], grandchildren_s[1] );
          }
        if ( !ntk.is_complemented( grandchildren_s[1] ) )
            return false;
        if ( ntk.level( grandchildren_n[0] ) == ntk.level( grandchildren_n[1] ) )
            return false;
        if ( ntk.is_on_critical_path( grandchildren_n[0] ) )
          return false;

        ntk.foreach_fanin( grandchildren_n[1], [&]( signal const& grandgrandchild ){   
              grandgrandchildren.emplace_back( grandgrandchild ); 
          } );

        if ( grandgrandchildren.size() != 2 )
            return false;
        if ( ntk.level( ntk.get_node( grandgrandchildren[0] ) ) > ntk.level( ntk.get_node( grandgrandchildren[1] ) ) )
          {
            std::swap( grandgrandchildren[0], grandgrandchildren[1] );
          }
        if ( ntk.level( ntk.get_node( grandgrandchildren[0] ) ) == ntk.level( ntk.get_node( grandgrandchildren[1] ) ) )
            return false;
        if ( ntk.is_on_critical_path( ntk.get_node( grandgrandchildren[0] ) ) )
          return false;
        if ( ntk.level( ntk.get_node( grandgrandchildren[1] ) ) <= ntk.level( children_n[0] ) )
            return false;
        and_left = ntk.create_and( grandgrandchildren[0], children_s[0] );
        and_right = !ntk.create_and( !grandchildren_s[0], children_s[0] );
        and_middle = !ntk.create_and( and_left, grandgrandchildren[1] );
        and_up = !ntk.create_and( and_middle, and_right );
        ntk.substitute_node( n, and_up );
        return true;
      }
    else
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

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
