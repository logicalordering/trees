package trees.pavt;

import java.util.Comparator;

/**
 * Implementation of concurrent BST tree based on the paper 
 * "Practical Concurrent Traversals in Search Trees" by 
 * Dana Drachsler-Cohen (ETH), Martin Vechev (ETH) and Eran Yahav (Technion).
 *
 * Copyright 2013 Dana Drachsler-Cohen (ddana [at] inf [dot] ethz [dot] ch).
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it wfill be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Dana Drachsler-Cohen
 */
public class PaVTBST <K,V> {
	
	protected PaVTNode<K, V> root;
	private Comparator<? super K> comparator;
	private PaVTNode<K, V> rightSentinel;
	private PaVTNode<K, V> leftSentinel;
	
	
	public PaVTBST(K min, K max) {
		rightSentinel = new PaVTNode<K, V>(min);
		leftSentinel = new PaVTNode<K, V>(max);
		leftSentinel.parent = rightSentinel;
		rightSentinel.right = leftSentinel;
		leftSentinel.leftSnapshot = rightSentinel;
		rightSentinel.rightSnapshot = leftSentinel;
		root = leftSentinel;
	}
	
	@SuppressWarnings("unchecked")
	private Comparable<? super K> comparable(final Object key) {
		if (key == null) {
			throw new NullPointerException();
		}
		if (comparator == null) {
			return (Comparable<? super K>)key;
		}
		return new Comparable<K>() {
			final Comparator<? super K> _cmp = comparator;

			@SuppressWarnings("unchecked")
			public int compareTo(final K rhs) { return _cmp.compare((K)key, rhs); }
		};
	}
	
	public V add(final K val, final V item) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTNode<K, V> node = root;
			PaVTNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					child = node.left;
				} else {
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res == 0) {
				V item2 = (V) node.item;
				return item2;
			}
			boolean leftLast = res < 0;
			synchronized(node) {
				if (node.marked || (leftLast && node.left != null) || (!leftLast && node.right != null)) {
					continue;
				}
				PaVTNode<K, V> upperNode = leftLast? node.leftSnapshot : node.rightSnapshot;
				if ((leftLast && (value.compareTo(upperNode.value) <= 0)) || 
						(!leftLast && (value.compareTo(upperNode.value) >= 0)
								)) {
					continue;
				}
				PaVTNode<K, V> newNode = new PaVTNode<K, V>(val, item, node, res > 0? node : upperNode, res > 0? upperNode : node);

				if (!leftLast) {
					upperNode.leftSnapshot = newNode;
					node.rightSnapshot = newNode;
					node.right = newNode;
					return null;
				}
				upperNode.rightSnapshot = newNode;
				node.leftSnapshot = newNode;
				node.left = newNode;
				return null;
			}
		}
	}
	
	public V remove(K val) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTNode<K, V> node = root;
			PaVTNode<K, V> leftNode = leftSentinel;
			PaVTNode<K, V> rightNode = rightSentinel;
			PaVTNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					leftNode = node;
					child = node.left;
				} else {
					rightNode = node;
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res != 0) {
				boolean leftLast = res < 0;
				PaVTNode<K, V> ref = leftLast? node.leftSnapshot: node.rightSnapshot; 
				if (
						(leftLast && value.compareTo(ref.value) <= 0) || 
						(!leftLast && value.compareTo(ref.value) >= 0)) {
					continue;
				}
				return null;
			}
			PaVTNode<K, V> parent = node.parent;
			synchronized(parent) {
				if (node.parent != parent) {
					if (node.marked) return null;
					continue;
				}
				synchronized(node) {
					if (node.marked) {
						return null;
					}
					PaVTNode<K, V> left = node.left;
					PaVTNode<K, V> right = node.right;
					boolean leftChild = parent.left == node;
					if (left == null && right == null) {
						rightNode = node.leftSnapshot;
						leftNode = node.rightSnapshot;
						node.marked = true;
						if (leftChild) {
							parent.left = null;
							parent.leftSnapshot = rightNode;
							rightNode.rightSnapshot = parent;
						} else {
							parent.right = null;
							parent.rightSnapshot = leftNode;
							leftNode.leftSnapshot = parent;
						}
					} else if (left == null || right == null) {
						child = left == null? right : left;
						rightNode = node.leftSnapshot;
						leftNode = node.rightSnapshot;
						synchronized(child) {
							PaVTNode<K, V> snapshotToLock = left == null? leftNode : rightNode;
							synchronized(snapshotToLock) {
								if ((left == null && snapshotToLock.leftSnapshot != node) ||
										(left != null && snapshotToLock.rightSnapshot != node) || 
										snapshotToLock.marked) {
									continue;
								}
								node.marked = true;
								child = left == null? right : left;
								if (leftChild) {
									parent.left = child;
								} else {
									parent.right = child;
								}
								child.parent = parent;
								rightNode.rightSnapshot = leftNode;
								leftNode.leftSnapshot = rightNode;
							}
						}
					} else {
						synchronized(left) {
							synchronized(right) {
								rightNode = node.leftSnapshot;
								leftNode = node.rightSnapshot;
								synchronized(rightNode) {
									if (rightNode.rightSnapshot != node || rightNode.marked) continue;
									if (right.left == null) {
										node.marked = true;
										right.left = left;
										left.parent = right;
										right.parent = parent;
										if (leftChild) {
											parent.left = right;
										} else {
											parent.right = right;
										}
										rightNode.rightSnapshot = leftNode;
										leftNode.leftSnapshot = rightNode;
									} else {
										PaVTNode<K, V> succ = leftNode;
										PaVTNode<K, V> succParent = succ.parent;
										synchronized(succParent) {
											if (leftNode.parent != succParent || leftNode.marked) continue;
											synchronized(leftNode) {
												if (leftNode.leftSnapshot != node || leftNode.marked) continue;
												PaVTNode<K, V> succRight = succ.right;
												if (succRight != null) {
													synchronized(succRight) {
														PaVTNode<K, V> succRightSnapshot = succ.rightSnapshot;
														if (succRightSnapshot != succRight) {
															synchronized(succRightSnapshot) {
																if (succRightSnapshot.leftSnapshot != succ || succRightSnapshot.marked) {
																	continue;
																}
																applyRemove(rightNode, node, parent, left, right,
																		leftChild, succ, succParent, succRight, succRightSnapshot);
															}
														} else {
															applyRemove(rightNode, node, parent, left, right,
																	leftChild, succ, succParent, succRight, succRightSnapshot);
														}
													}
												} else {
													PaVTNode<K, V> succRightSnapshot = succ.rightSnapshot;
													applyRemove(rightNode, node, parent, left, right,
															leftChild, succ, succParent, succRight, succRightSnapshot);
												}											
											}
										}
									}
								}	
							}
						}
					}
				}
			}
			return (V) node.item;
		}
	}

	protected void applyRemove(PaVTNode<K, V> rightNode,
			PaVTNode<K, V> node,
			PaVTNode<K, V> parent,
			PaVTNode<K, V> left,
			PaVTNode<K, V> right, boolean leftChild,
			PaVTNode<K, V> succ,
			PaVTNode<K, V> succParent,
			PaVTNode<K, V> succRight,
			PaVTNode<K, V> succRightSnapshot) {
		node.marked = true;
		succ.right = right;
		right.parent = succ;
		succ.left = left;
		left.parent = succ;
		succ.parent = parent;
		if (leftChild) {
			parent.left = succ;
		} else {
			parent.right = succ;
		}
		succParent.left = succRight;
		succ.rightSnapshot = succRightSnapshot;
		succRightSnapshot.leftSnapshot = succ;
		if (succRight != null) {
			succRight.parent = succParent;
		} 
		succ.leftSnapshot = rightNode;
		rightNode.rightSnapshot = succ;
	}

	public boolean contains(K val) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTNode<K, V> node = root;
			PaVTNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					child = node.left;
				} else {
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res == 0) {
				return true;
			}
			PaVTNode<K, V> upperNode = res < 0? node.leftSnapshot : node.rightSnapshot;
			
			if (
					(res < 0 && (value.compareTo(upperNode.value) <= 0)) || 
					(res > 0 && (value.compareTo(upperNode.value) >= 0))
					) {
				continue;
			}
			
			return false;
		}
	}


	public int size() {
        PaVTNode<K, V> n = root.left;
        return size(n);
    }

	private int size(PaVTNode<K, V> n) {
		if (n == null) return 0;
        return 1 + size(n.left) +  size(n.right);
    }
	
	class PaVTNode<K, V> {
		
		public final K value;
		public final Object item;
		public volatile PaVTNode<K, V> leftSnapshot;
		public volatile PaVTNode<K, V> rightSnapshot;
		
		public volatile boolean marked = false;
		
		public PaVTNode<K, V> parent;
		public volatile PaVTNode<K, V> right;
		public volatile PaVTNode<K, V> left;
		
		public PaVTNode(K value) {
			this(value, null);
		}
		
		public PaVTNode(K value, Object item) {
			this.value = value;
			this.item = item;
			this.marked = false;
		}
		
		public PaVTNode(K val, V item2, PaVTNode<K, V> parent,
				PaVTNode<K, V> leftSnapshot, PaVTNode<K, V> rightSnapshot) {
			this(val, item2);
			this.parent = parent;
			this.leftSnapshot = leftSnapshot;
			this.rightSnapshot = rightSnapshot;
		}

		@Override
		public String toString() {
			String delimiter = "  ";
			StringBuilder sb = new StringBuilder();
			return sb.append(value + (marked? "(marked)" : "") + delimiter).toString();
		}

	}

}
